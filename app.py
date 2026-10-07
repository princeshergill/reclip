import os
import uuid
import glob
import json
import subprocess
import threading
import ipaddress
import socket
import urllib.error
import urllib.request
from urllib.parse import urlparse
from flask import Flask, request, jsonify, send_file, render_template, Response

app = Flask(__name__)
DOWNLOAD_DIR = os.path.join(os.path.dirname(__file__), "downloads")
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

jobs = {}

# Direct audio URLs found by yt-dlp, keyed by a short id, so the page can preview
# a link before downloading it. Only URLs that yt-dlp itself extracted are ever fetched.
streams = {}
STREAMABLE_PROTOCOLS = {"http", "https"}  # plain files; HLS/DASH fragments can't be proxied simply


def is_public_http_url(url):
    """True only for http(s) URLs whose host resolves to public addresses.

    The preview proxy fetches URLs that yt-dlp extracted from a page the user submitted, and a
    hostile page can make yt-dlp return any URL. Refuse loopback, private, link-local and other
    internal addresses so ReClip can't be used to reach services on this machine or network.
    Set RECLIP_ALLOW_PRIVATE_STREAMS=1 to allow them (for example to preview from a LAN server).
    """
    if os.environ.get("RECLIP_ALLOW_PRIVATE_STREAMS") == "1":
        return True
    try:
        p = urlparse(url)
        if p.scheme not in ("http", "https") or not p.hostname:
            return False
        port = p.port or (443 if p.scheme == "https" else 80)
        for family, _type, _proto, _canon, sockaddr in socket.getaddrinfo(p.hostname, port, proto=socket.IPPROTO_TCP):
            ip = ipaddress.ip_address(sockaddr[0].split("%")[0])
            if (ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved
                    or ip.is_multicast or ip.is_unspecified):
                return False
        return True
    except (ValueError, OSError):
        return False


class _CheckedRedirects(urllib.request.HTTPRedirectHandler):
    """Follow redirects only to public addresses."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if not is_public_http_url(newurl):
            raise urllib.error.HTTPError(newurl, 403, "Blocked address", headers, fp)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


_opener = urllib.request.build_opener(_CheckedRedirects)


def register_stream(url, info):
    """Remember a directly-playable audio stream, and a combined video+audio one when the
    source offers it. Returns (audio_stream_id, video_stream_id); either may be None."""
    best = None
    for f in info.get("formats", []):
        if not f.get("url") or f.get("acodec") in (None, "none"):
            continue
        if f.get("protocol") not in STREAMABLE_PROTOCOLS:
            continue
        audio_only = f.get("vcodec") in (None, "none")
        score = (audio_only, f.get("abr") or 0, f.get("tbr") or 0)
        if best is None or score > best[0]:
            best = (score, f)
    if best is None and info.get("url") and info.get("protocol") in STREAMABLE_PROTOCOLS:
        best = (None, info)  # single-file result (e.g. a direct media link)
    def remember(f):
        if not is_public_http_url(f["url"]):
            return None
        sid = uuid.uuid4().hex[:12]
        streams[sid] = {
            "url": f["url"],
            "headers": f.get("http_headers") or info.get("http_headers") or {},
            "source": url,
        }
        return sid

    # A single file with both picture and sound, in a format browsers play (mp4/webm), up to 720p.
    video = None
    for f in info.get("formats", []):
        if not f.get("url") or f.get("protocol") not in STREAMABLE_PROTOCOLS:
            continue
        if f.get("vcodec") in (None, "none") or f.get("acodec") in (None, "none"):
            continue
        if f.get("ext") not in ("mp4", "webm"):
            continue
        h = f.get("height") or 0
        if h > 720:
            continue
        if video is None or h > (video.get("height") or 0):
            video = f

    # No combined file (YouTube usually serves picture and sound separately): pair the best
    # picture-only stream with a matching sound-only stream. The server joins them on the fly
    # with ffmpeg (no re-encoding) when the preview is played.
    mux = None
    if video is None:
        def usable(f):
            return f.get("url") and f.get("protocol") in STREAMABLE_PROTOCOLS
        pics = [f for f in info.get("formats", [])
                if usable(f) and f.get("vcodec") not in (None, "none") and f.get("acodec") in (None, "none")
                and f.get("ext") in ("mp4", "webm") and 0 < (f.get("height") or 0) <= 720]
        sounds = [f for f in info.get("formats", [])
                  if usable(f) and f.get("vcodec") in (None, "none") and f.get("acodec") not in (None, "none")]
        # Prefer H.264 + AAC (plays everywhere), then whatever pairs up.
        pics.sort(key=lambda f: ((f.get("vcodec") or "").startswith("avc1"), f.get("height") or 0), reverse=True)
        if pics and sounds:
            pic = pics[0]
            want_aac = (pic.get("vcodec") or "").startswith("avc1")
            sounds.sort(key=lambda f: ((f.get("acodec") or "").startswith("mp4a") == want_aac, f.get("abr") or 0), reverse=True)
            mux = (pic, sounds[0])

    def remember_mux(pic, snd):
        if not (is_public_http_url(pic["url"]) and is_public_http_url(snd["url"])):
            return None
        sid = uuid.uuid4().hex[:12]
        streams[sid] = {
            "mux": True,
            "video": {"url": pic["url"], "headers": pic.get("http_headers") or info.get("http_headers") or {}},
            "audio": {"url": snd["url"], "headers": snd.get("http_headers") or info.get("http_headers") or {}},
            "source": url,
        }
        return sid

    video_id = remember(video) if video else (remember_mux(*mux) if mux else None)
    return (remember(best[1]) if best else None, video_id, bool(mux and not video and video_id))


def parse_ytdlp_json(stdout):
    """Parse yt-dlp JSON output.

    With ``-j`` yt-dlp prints one JSON object per line. Some extractors
    emit multiple videos even with ``--no-playlist``, so stdout contains
    several objects and a plain ``json.loads`` raises "Extra data".
    Return the first valid object.
    """
    for line in stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        return json.loads(line)
    raise ValueError("yt-dlp returned no data")


def run_download(job_id, url, format_choice, format_id):
    job = jobs[job_id]
    out_template = os.path.join(DOWNLOAD_DIR, f"{job_id}.%(ext)s")

    cmd = ["yt-dlp", "--no-playlist", "-o", out_template]

    if format_choice == "audio":
        cmd += ["-x", "--audio-format", "mp3"]
    elif format_id:
        cmd += ["-f", f"{format_id}+bestaudio/best", "--merge-output-format", "mp4"]
    else:
        cmd += ["-f", "bestvideo+bestaudio/best", "--merge-output-format", "mp4"]

    cmd.append(url)

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        if result.returncode != 0:
            job["status"] = "error"
            job["error"] = result.stderr.strip().split("\n")[-1]
            return

        files = glob.glob(os.path.join(DOWNLOAD_DIR, f"{job_id}.*"))
        if not files:
            job["status"] = "error"
            job["error"] = "Download completed but no file was found"
            return

        if format_choice == "audio":
            target = [f for f in files if f.endswith(".mp3")]
            chosen = target[0] if target else files[0]
        else:
            target = [f for f in files if f.endswith(".mp4")]
            chosen = target[0] if target else files[0]

        for f in files:
            if f != chosen:
                try:
                    os.remove(f)
                except OSError:
                    pass

        job["status"] = "done"
        job["file"] = chosen
        ext = os.path.splitext(chosen)[1]
        title = job.get("title", "").strip()
        # Sanitize title for filename
        if title:
            safe_title = "".join(c for c in title if c not in r'\/:*?"<>|').strip()[:100].strip()
            job["filename"] = f"{safe_title}{ext}" if safe_title else os.path.basename(chosen)
        else:
            job["filename"] = os.path.basename(chosen)
    except subprocess.TimeoutExpired:
        job["status"] = "error"
        job["error"] = "Download timed out (5 min limit)"
    except Exception as e:
        job["status"] = "error"
        job["error"] = str(e)


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/info", methods=["POST"])
def get_info():
    data = request.json
    url = data.get("url", "").strip()
    if not url:
        return jsonify({"error": "No URL provided"}), 400

    cmd = ["yt-dlp", "--no-playlist", "-j", url]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            return jsonify({"error": result.stderr.strip().split("\n")[-1]}), 400

        info = parse_ytdlp_json(result.stdout)

        # Build quality options — keep best format per resolution
        best_by_height = {}
        for f in info.get("formats", []):
            height = f.get("height")
            if height and f.get("vcodec", "none") != "none":
                tbr = f.get("tbr") or 0
                if height not in best_by_height or tbr > (best_by_height[height].get("tbr") or 0):
                    best_by_height[height] = f

        formats = []
        for height, f in best_by_height.items():
            formats.append({
                "id": f["format_id"],
                "label": f"{height}p",
                "height": height,
            })
        formats.sort(key=lambda x: x["height"], reverse=True)

        stream_id, video_stream_id, video_mux = register_stream(url, info)

        return jsonify({
            "title": info.get("title", ""),
            "thumbnail": info.get("thumbnail", ""),
            "duration": info.get("duration"),
            "uploader": info.get("uploader", ""),
            "formats": formats,
            "stream_id": stream_id,
            "video_stream_id": video_stream_id,
            "video_mux": video_mux,
        })
    except subprocess.TimeoutExpired:
        return jsonify({"error": "Timed out fetching video info"}), 400
    except Exception as e:
        return jsonify({"error": str(e)}), 400


@app.route("/api/playlist", methods=["POST"])
def get_playlist_info():
    data = request.json
    url = data.get("url", "").strip()
    if not url:
        return jsonify({"error": "No URL provided"}), 400

    cmd = ["yt-dlp", "--flat-playlist", "-J", url]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            return jsonify({"error": result.stderr.strip().split("\n")[-1]}), 400

        info = json.loads(result.stdout)
        entries = info.get("entries", [])
        urls = [entry.get("url") for entry in entries if entry.get("url")]
        return jsonify({"urls": urls})
    except subprocess.TimeoutExpired:
        return jsonify({"error": "Timed out fetching playlist info"}), 400
    except Exception as e:
        return jsonify({"error": str(e)}), 400


@app.route("/api/download", methods=["POST"])
def start_download():
    data = request.json
    url = data.get("url", "").strip()
    format_choice = data.get("format", "video")
    format_id = data.get("format_id")
    title = data.get("title", "")

    if not url:
        return jsonify({"error": "No URL provided"}), 400

    job_id = uuid.uuid4().hex[:10]
    jobs[job_id] = {"status": "downloading", "url": url, "title": title}

    thread = threading.Thread(target=run_download, args=(job_id, url, format_choice, format_id))
    thread.daemon = True
    thread.start()

    return jsonify({"job_id": job_id})


@app.route("/api/status/<job_id>")
def check_status(job_id):
    job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404
    return jsonify({
        "status": job["status"],
        "error": job.get("error"),
        "filename": job.get("filename"),
    })


@app.route("/api/file/<job_id>")
def download_file(job_id):
    job = jobs.get(job_id)
    if not job or job["status"] != "done":
        return jsonify({"error": "File not ready"}), 404
    return send_file(job["file"], as_attachment=True, download_name=job["filename"])


def mux_preview(s):
    """Join a picture-only and a sound-only stream into one fragmented MP4 and stream it.
    No re-encoding. ?start=SECONDS restarts the stream from that point (used for seeking)."""
    start = request.args.get("start", default=0.0, type=float) or 0.0
    start = max(0.0, min(start, 6 * 3600.0))

    if not (is_public_http_url(s["video"]["url"]) and is_public_http_url(s["audio"]["url"])):
        return jsonify({"error": "Blocked address"}), 403

    def hdrs(h):
        return "".join(f"{k}: {v}\r\n" for k, v in h.items())

    cmd = ["ffmpeg", "-hide_banner", "-loglevel", "error"]
    for part in (s["video"], s["audio"]):
        if start > 0:
            cmd += ["-ss", f"{start:.2f}"]
        if part["headers"]:
            cmd += ["-headers", hdrs(part["headers"])]
        # network only: never let ffmpeg open local files or other protocols from a hostile playlist
        cmd += ["-protocol_whitelist", "http,https,tcp,tls,crypto", "-i", part["url"]]
    cmd += ["-map", "0:v:0", "-map", "1:a:0", "-c", "copy",
            "-movflags", "frag_keyframe+empty_moov+default_base_moof", "-f", "mp4", "pipe:1"]
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL)
    except OSError:
        return jsonify({"error": "ffmpeg is not available"}), 502

    def generate():
        try:
            while True:
                chunk = proc.stdout.read(64 * 1024)
                if not chunk:
                    break
                yield chunk
        finally:  # the browser went away or the stream ended: stop ffmpeg
            proc.kill()
            proc.wait()

    return Response(generate(), mimetype="video/mp4", headers={"Cache-Control": "no-store", "Accept-Ranges": "none"})


@app.route("/api/stream/<stream_id>")
def stream_preview(stream_id):
    """Proxy the audio of a not-yet-downloaded link so the player can preview it.
    Forwards Range requests so seeking works."""
    s = streams.get(stream_id)
    if not s:
        return jsonify({"error": "Preview not available"}), 404
    if s.get("mux"):
        return mux_preview(s)
    if not is_public_http_url(s["url"]):
        return jsonify({"error": "Blocked address"}), 403
    headers = dict(s["headers"])
    if request.headers.get("Range"):
        headers["Range"] = request.headers["Range"]
    try:
        upstream = _opener.open(urllib.request.Request(s["url"], headers=headers), timeout=20)
    except urllib.error.HTTPError as e:
        upstream = e  # e.g. 206/416/403: pass the status through
    except Exception:
        return jsonify({"error": "Could not reach the source"}), 502

    def generate():
        try:
            while True:
                chunk = upstream.read(64 * 1024)
                if not chunk:
                    break
                yield chunk
        finally:
            upstream.close()

    resp = Response(generate(), status=upstream.status if hasattr(upstream, "status") else upstream.code)
    for h in ("Content-Type", "Content-Length", "Content-Range", "Accept-Ranges"):
        if upstream.headers.get(h):
            resp.headers[h] = upstream.headers[h]
    resp.headers.setdefault("Accept-Ranges", "bytes")
    return resp


@app.route("/api/play/<job_id>")
def play_file(job_id):
    """Stream a finished download inline (no attachment header) so the browser
    player can play and seek it. Only files from completed jobs are served."""
    job = jobs.get(job_id)
    if not job or job["status"] != "done":
        return jsonify({"error": "File not ready"}), 404
    return send_file(job["file"], conditional=True)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8899))
    host = os.environ.get("HOST", "127.0.0.1")
    app.run(host=host, port=port)
