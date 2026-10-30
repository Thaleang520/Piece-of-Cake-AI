"""Khmer Dubber Editor - single-file Flask website.

Run:  pip install flask faster-whisper edge-tts deep-translator imageio-ffmpeg numpy
      python khmer_dubber_web.py     then open http://127.0.0.1:5000
"""
"""core.py - the ORIGINAL helpers and pipeline of Khmer Dubber, copied unchanged from Test.py
(only the Tk window code was removed).  The Flask server (app.py) calls these."""
import asyncio, copy, glob, hashlib, importlib, importlib.util, json, math, os, queue, re
import shutil, subprocess, sys, tempfile, threading, time, wave, zipfile, zlib

VOICES = {"Female (Sreymom)": "km-KH-SreymomNeural", "Male (Piseth)": "km-KH-PisethNeural"}
ACCURACY = {"Fast": "base", "Balanced": "small", "Best (slower)": "medium"}
STEPS = ["Listen to the Chinese speech", "Translate to Khmer",
         "Make the Khmer voice", "Build the new video"]
SPEEDS = ["Auto", "0.7x", "0.8x", "0.9x", "1.0x", "1.1x", "1.2x", "1.3x", "1.5x", "1.7x", "2.0x"]

KHMER_FONT = "Leelawadee UI" if sys.platform.startswith("win") else "Noto Sans Khmer"
# ---- colours ---------------------------------------------------------------
BG, PANEL, PANEL2, PANEL_ALT = "#0a0a0c", "#121215", "#1a1a1f", "#0f0f12"
LINE, HOVER = "#26262c", "#24232a"
FG, MUTED = "#f3efe6", "#8d887c"
ACCENT, ACCENT_H, ACCENT_L = "#c9a45c", "#b58f47", "#e6cf9a"      # champagne gold
ACCENT_FG = "#15110a"                                             # dark text on gold
OK, GOLD, VIDEO_BG = "#7fd6a4", "#e6cf9a", "#050506"
WARN_BG, WARN_LINE = "#211b0d", "#5a4a22"
BLOCK, BLOCK_EDGE, BLOCK_MUTE, BLOCK_MUTE_EDGE = "#3a3220", "#6e5a30", "#232327", "#3a3a40"
REF_FILL, REF_EDGE = "#141418", "#25252b"
PLAYHEAD = "#e8d3a0"
UI_FONTS = ("Segoe UI Variable Display", "Segoe UI Variable Text", "Segoe UI", "SF Pro Display", "Helvetica Neue",
            "Noto Sans", "DejaVu Sans")

# ---- timeline layout -------------------------------------------------------
RULER_H, ZH_Y, ZH_H, KM_Y, KM_H = 24, 32, 34, 74, 50
TL_H = KM_Y + KM_H + 14

REQUIRED = [("faster_whisper", "faster-whisper"), ("edge_tts", "edge-tts"),
            ("deep_translator", "deep-translator")]


class Cancelled(Exception):
    pass


# =============================================================== helpers
def fmt_time(sec):
    sec = max(0, int(sec))
    if sec >= 3600:
        return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"
    return f"{sec // 60:02d}:{sec % 60:02d}"


def parse_time(text):
    """'10:00' -> 600, '1:02:03' -> 3723, '90' -> 90. Returns None if it is not a time."""
    try:
        secs = 0.0
        for part in text.strip().split(":"):
            secs = secs * 60 + float(part)
        return secs
    except ValueError:
        return None


def parse_range(text):
    """'10:00-20:00' -> (600, 1200). '10:00-' -> (600, None). '' -> (0, None) = whole video.
    Returns False if the text cannot be understood."""
    text = (text or "").strip().replace(" ", "")
    if not text:
        return 0.0, None
    for sep in ("-", "~", "\u2013", "to"):
        if sep in text:
            a, b = text.split(sep, 1)
            break
    else:
        return False
    start = parse_time(a) if a else 0.0
    end = parse_time(b) if b else None
    if start is None or (b and end is None) or start < 0:
        return False
    if end is not None and end <= start:
        return False
    return start, end


def shorten(text, n=70):
    return text if len(text) <= n else text[:n - 3] + "..."


def srt_time(t):
    ms = int(round(max(t, 0) * 1000))
    h, ms = divmod(ms, 3600000)
    m, ms = divmod(ms, 60000)
    s, ms = divmod(ms, 1000)
    return f"{h:02d}:{m:02d}:{s:02d},{ms:03d}"


def to_srt(segs):
    out, n = [], 0
    for sg in segs:
        text = (sg.get("km") or "").strip()
        if not text or text == "...":
            continue
        n += 1
        out.append(f"{n}\n{srt_time(sg['start'])} --> {srt_time(sg['end'])}\n{text}\n")
    return "\n".join(out)


def merge_segments(segs, max_chars=60, max_gap=0.8, max_len=12.0):
    """Whisper often cuts a sentence in the middle. Glue those pieces together so the
    translator gets whole sentences (much better Khmer) and the voice sounds natural."""
    out = []
    for sg in segs:
        if out:
            prev = out[-1]
            ends = prev["zh"].rstrip()[-1:] in "\u3002\uff01\uff1f!?\u2026\uff1b;."
            if (not ends and sg["start"] - prev["end"] <= max_gap
                    and len(prev["zh"]) + len(sg["zh"]) <= max_chars
                    and sg["end"] - prev["start"] <= max_len):
                prev["zh"] += sg["zh"]
                prev["end"] = sg["end"]
                continue
        out.append(dict(sg))
    return out


def plan_voice(segs, durs, shift=0.0, gap=0.08):
    """Decide when each Khmer clip starts and how much to speed it up.
    durs[i] = length in seconds of the Khmer clip for segs[i] (None = no clip).
    Normal lines may use the free time up to the next line. Lines marked "locked"
    (resized by the user, or 'Fit exactly in block') must fit inside their own block.
    A manual speed on a line overrides the automatic speed.
    Returns a list of (index, start_seconds, speed_ratio)."""
    plan, cursor = [], 0.0
    for i, seg in enumerate(segs):
        dur = durs[i]
        if not dur:
            continue
        want = max(seg["start"] + shift, 0.0)
        start = max(want, cursor)
        if seg.get("locked"):
            nxt = seg["end"] + shift
        elif i + 1 < len(segs):
            nxt = segs[i + 1]["start"] + shift
        else:
            nxt = seg["end"] + shift + 3
        avail = max(nxt - start - gap, 0.5)
        manual = float(seg.get("speed") or 0)
        if manual > 0:
            ratio = min(max(manual, 0.5), 4.0)
        else:
            ratio = 1.0
            if dur > avail * 1.03:
                ratio = min(dur / avail, 2.5 if start - want > 1.0 else 2.0)
                if seg.get("locked"):
                    ratio = min(dur / avail, 3.0)
        plan.append((i, start, ratio))
        cursor = start + dur / ratio + gap
    return plan


def tempo_filter(r):
    r = min(max(r, 0.5), 4.0)
    parts = []
    while r > 2.0:
        parts.append("atempo=2.0")
        r /= 2.0
    parts.append(f"atempo={r:.3f}")
    return ",".join(parts)


MALE_VOICE, FEMALE_VOICE = "Male (Piseth)", "Female (Sreymom)"
PITCH_SPLIT_HZ = 165.0          # average voice pitch below this = male, above = female


def estimate_pitch(x, sr=16000):
    """Median voice pitch (Hz) of a mono float array, or None if there is no clear voice.
    Simple autocorrelation on short frames; good enough to tell male from female."""
    import numpy as np
    n, hop = int(sr * 0.04), int(sr * 0.02)
    if len(x) < n * 3:
        return None
    lo, hi = int(sr / 400), int(sr / 70)            # search 70 - 400 Hz
    frames = [x[i:i + n] for i in range(0, len(x) - n, hop)]
    rms = np.array([float(np.sqrt(np.mean(f ** 2))) for f in frames])
    gate = max(float(np.percentile(rms, 60)) * 0.6, 0.005)
    win = np.hanning(n)
    pitches = []
    for f, e in zip(frames, rms):
        if e < gate:
            continue
        f = (f - f.mean()) * win
        spec = np.fft.rfft(f, 2048)
        ac = np.fft.irfft(spec * np.conj(spec))[:hi + 2]
        if ac[0] <= 0:
            continue
        ac = ac / ac[0]
        top = float(ac[lo:hi].max())
        if top < 0.35:                              # not a voiced (vowel) frame
            continue
        lag = None
        for i in range(lo + 1, hi):                 # first strong peak = real pitch period
            if ac[i] > ac[i - 1] and ac[i] >= ac[i + 1] and ac[i] >= 0.85 * top:
                lag = i
                break
        if lag:
            pitches.append(sr / lag)
    if len(pitches) < 5:
        return None
    return float(np.median(pitches))


def detect_voice(audio, start, end, sr=16000):
    """Return the Khmer voice name that matches the speaker (None if unsure)."""
    a, b = int(max(start, 0) * sr), int(max(end, 0) * sr)
    f0 = estimate_pitch(audio[a:b], sr)
    if f0 is None:
        return None
    return MALE_VOICE if f0 < PITCH_SPLIT_HZ else FEMALE_VOICE


ZH_END = "\u3002\uff01\uff1f!?\u2026\uff1b;."
KM_END = "\u17d4\u17d5!?"                      # Khmer full stops and ! ?
CLOSE_MARKS = "\u201d\u2019\u300d\u300f\uff09)\"'"


def split_units(text, ends):
    """Cut a text at every line break and every sentence end. Keeps the punctuation."""
    out = []
    for ln in [x.strip() for x in (text or "").split("\n") if x.strip()]:
        cur, n = "", len(ln)
        for i, ch in enumerate(ln):
            cur += ch
            if ch not in ends:
                continue
            if ch == "." and 0 < i < n - 1 and ln[i - 1].isdigit() and ln[i + 1].isdigit():
                continue                                    # 3.5 is not a sentence end
            nxt = ln[i + 1] if i + 1 < n else ""
            if nxt and (nxt in ends or nxt in CLOSE_MARKS):
                continue                                    # "?!" or a closing quote follows
            out.append(cur.strip())
            cur = ""
        if cur.strip():
            out.append(cur.strip())

    def real(x):
        return sum(1 for c in x if c not in ends and c not in CLOSE_MARKS and not c.isspace())
    glued = []
    for x in out:                                           # tiny leftovers join a neighbour
        if glued and (real(x) < 2 or real(glued[-1]) < 2):
            glued[-1] += (" " if ends is KM_END else "") + x
        else:
            glued.append(x)
    return glued


def cut_text(text, weights):
    """Cut a text into len(weights) pieces sized like the weights, preferring to cut right
    after a comma or full stop that is close to the ideal place."""
    n, L = len(weights), len(text)
    if n < 2 or L < n:
        return [text] + [""] * (n - 1)
    total, acc, prev, cuts = float(sum(weights)), 0, 0, []
    for w in weights[:-1]:
        acc += w
        target = round(L * acc / total)
        best = target
        for d in range(0, 9):
            hit = next((i for i in (target - d, target + d)
                        if 0 < i < L and text[i - 1] in "\uff0c,\u3001\u3002\uff01\uff1f\uff1b;!?"),
                       None)
            if hit:
                best = hit
                break
        best = min(max(best, prev + 1), L - (n - len(cuts) - 1))
        cuts.append(best)
        prev = best
    edges = [0] + cuts + [L]
    return [text[edges[i]:edges[i + 1]].strip() for i in range(n)]


def split_lines(segs):
    """A box that holds 2 or 3 sentences / lines becomes 2 or 3 boxes. The cut is made at
    line breaks and at sentence ends (Chinese and Khmer). The time is shared by length.
    A piece that has no Khmer yet gets '...' (it is translated by the app)."""
    out = []
    for sg in segs:
        km = sg.get("km") or ""
        km = "" if km == "..." else km
        kl = split_units(km, KM_END)
        zl = split_units(sg.get("zh") or "", ZH_END)
        if max(len(kl), len(zl)) < 2:
            out.append(sg)
            continue
        if len(kl) >= 2:                                    # the voice is Khmer: follow it
            n, base = len(kl), kl
        else:
            n, base = len(zl), zl
        weights = [max(len(x), 1) for x in base]
        if len(zl) != n:
            zl = cut_text("".join(zl), weights)
        if len(kl) != n:
            kl = ["..."] * n                                # to be translated again
        tot, acc = float(sum(weights)), 0.0
        a, b = sg["start"], sg["end"]
        oa, ob = sg.get("os", a), sg.get("oe", b)
        for k in range(n):
            f0, f1 = acc / tot, (acc + weights[k]) / tot
            acc += weights[k]
            ns = dict(sg)
            ns.update(zh=zl[k], km=kl[k] or "...",
                      start=a + (b - a) * f0, end=a + (b - a) * f1,
                      os=oa + (ob - oa) * f0, oe=oa + (ob - oa) * f1)
            out.append(ns)
    return out


PROJECT_MAGIC = b"KHDUB1\n"          # old project files (text only) start with this
CLIP_NAME = re.compile(r"^c_[0-9a-f]{16}\.(mp3|none)$")


def write_project(path, data, files=None):
    """One binary project file (.khdub): the lines and settings, plus the Khmer voice
    clips and (optionally) the finished dubbed video. `files` = {name in file: path}."""
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr("project.json", json.dumps(data, ensure_ascii=False))
        for arc, fp in (files or {}).items():
            packed = zipfile.ZIP_STORED if arc.endswith((".mp3", ".mp4")) else zipfile.ZIP_DEFLATED
            z.write(fp, arc, compress_type=packed)


def read_project(path, extract_to=None):
    """Read a project. Voice clips and the dubbed video are unpacked into `extract_to`."""
    with open(path, "rb") as f:
        head = f.read(len(PROJECT_MAGIC))
        f.seek(0)
        blob = f.read() if head == PROJECT_MAGIC else None
    if blob is not None:                                   # older text-only project
        return json.loads(zlib.decompress(blob[len(PROJECT_MAGIC):]).decode("utf-8"))
    try:
        z = zipfile.ZipFile(path)
    except zipfile.BadZipFile:
        raise ValueError("This is not a Khmer Dubber project file.")
    with z:
        data = json.loads(z.read("project.json").decode("utf-8"))
        if extract_to:
            for name in z.namelist():
                base = os.path.basename(name)
                if CLIP_NAME.match(base):
                    target = base
                elif base == "dubbed.mp4":
                    target = "loaded_dubbed.mp4"
                else:
                    continue
                with z.open(name) as src, open(os.path.join(extract_to, target), "wb") as dst:
                    shutil.copyfileobj(src, dst)
    return data


def find_ffmpeg():
    exe = shutil.which("ffmpeg")
    if exe:
        return exe
    try:
        import imageio_ffmpeg
        exe = imageio_ffmpeg.get_ffmpeg_exe()
        if exe and os.path.exists(exe):
            return exe
    except Exception:
        pass
    return None


def run_ffmpeg(args, cwd=None):
    exe = find_ffmpeg()
    if not exe:
        raise RuntimeError("FFmpeg was not found. Click 'Install now' on the first screen.")
    flags = subprocess.CREATE_NO_WINDOW if sys.platform.startswith("win") else 0
    p = subprocess.run([exe, "-y", "-loglevel", "error"] + args,
                       capture_output=True, text=True, creationflags=flags, cwd=cwd)
    if p.returncode != 0:
        raise RuntimeError(p.stderr.strip() or "ffmpeg failed")


def missing_packages():
    need = []
    for mod, pkg in REQUIRED:
        try:
            importlib.import_module(mod)
        except Exception:
            need.append(pkg)
    return need


def has_module(name):
    try:
        return importlib.util.find_spec(name) is not None
    except Exception:
        return False


def open_folder(path):
    folder = os.path.dirname(os.path.abspath(path))
    if sys.platform.startswith("win"):
        os.startfile(folder)
    elif sys.platform == "darwin":
        subprocess.Popen(["open", folder])
    else:
        subprocess.Popen(["xdg-open", folder])


def open_file(path):
    if sys.platform.startswith("win"):
        os.startfile(path)
    elif sys.platform == "darwin":
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


def open_srt(path):
    """Open a subtitle file for reading. Windows often has no program linked to .srt,
    so use Notepad there; other systems use their default viewer."""
    if sys.platform.startswith("win"):
        subprocess.Popen(["notepad.exe", path])
    else:
        open_file(path)


# ---------------------------------------------------------- translators
def google_fast(text):
    import urllib.parse
    import urllib.request
    url = ("https://translate.googleapis.com/translate_a/single"
           "?client=gtx&sl=zh-CN&tl=km&dt=t")
    req = urllib.request.Request(
        url, data=urllib.parse.urlencode({"q": text}).encode(),
        headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=25) as r:
        js = json.loads(r.read().decode("utf-8"))
    return "".join(part[0] for part in js[0] if part and part[0])


def ms_translate(texts):
    """Microsoft translator: every sentence is translated separately (no line mix-ups)."""
    import urllib.request
    ua = {"User-Agent": "Mozilla/5.0"}
    req = urllib.request.Request("https://edge.microsoft.com/translate/auth", headers=ua)
    with urllib.request.urlopen(req, timeout=15) as r:
        token = r.read().decode().strip()
    req = urllib.request.Request(
        "https://api-edge.cognitive.microsofttranslator.com/translate"
        "?from=zh-Hans&to=km&api-version=3.0",
        data=json.dumps([{"Text": t} for t in texts]).encode("utf-8"),
        headers={"Authorization": "Bearer " + token,
                 "Content-Type": "application/json", **ua})
    with urllib.request.urlopen(req, timeout=25) as r:
        js = json.loads(r.read().decode("utf-8"))
    out = [x["translations"][0]["text"].strip() for x in js]
    if len(out) != len(texts):
        raise ValueError("unexpected reply")
    return out


def translate_one(text, engine="microsoft"):
    """Translate one Chinese line to Khmer (used by the 'Re-translate' button)."""
    if engine == "microsoft":
        try:
            return ms_translate([text])[0]
        except Exception:
            pass
    try:
        out = google_fast(text)
        if out.strip():
            return out
    except Exception:
        pass
    from deep_translator import GoogleTranslator
    return GoogleTranslator(source="zh-CN", target="km").translate(text)




class Pipeline:
    """Holds what the original App object held for the worker code."""
    def __init__(self, workdir, post):
        self.workdir = workdir
        self._post = post
        self.cancel_flag = threading.Event()
        self.done_note = ""

    def _check(self):
        if self.cancel_flag.is_set():
            raise Cancelled()

    def _guard(self, fn, *args):
        try:
            fn(*args)
        except Cancelled:
            self._post("cancelled")
        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            if "metadata_errors" in tb:
                try:
                    self._post("step", 0, "Updating the 'av' library, please wait...", 1)
                    subprocess.run([sys.executable, "-m", "pip", "install", "--upgrade", "av"],
                                   check=True, capture_output=True)
                    self._post("error", "I updated the 'av' library to fix this.\n\n"
                                        "Please CLOSE the app and open it again, then try your video.")
                except Exception:
                    self._post("error", "Your 'av' library is too old. In Command Prompt run:\n\n"
                                        "pip install --upgrade av faster-whisper\n\n"
                                        "then open the app again.")
            else:
                tail = "\n".join(tb.strip().splitlines()[-6:])
                self._post("error", self._friendly(e) + "\n\nDetails:\n" + tail)

    @staticmethod
    def _friendly(e):
        msg = str(e)
        low = msg.lower()
        if any(k in low for k in ("connection", "network", "timeout", "resolve", "getaddrinfo")):
            return "Could not reach the internet. Translation and the Khmer voice need " \
                   "an internet connection.\n\n" + msg
        return msg

    def _background_only(self, video, wd, install_demucs, segs):
        """Make a copy of the original sound WITHOUT the human voice. Always returns a wav path.
        1) demucs (AI separation, best)  2) otherwise mute the original while people speak."""
        flags = subprocess.CREATE_NO_WINDOW if sys.platform.startswith("win") else 0
        self._post("step", 3, "Removing the original voice (keeping music and background)...", 94)
        src = os.path.join(wd, "orig44.wav")
        if not os.path.exists(src):
            run_ffmpeg(["-i", video, "-vn", "-af", "aresample=async=1:first_pts=0",
                        "-ac", "2", "-ar", "44100", src])
        self._check()

        have = has_module("demucs")
        why = ""
        if not have and install_demucs:
            self._post("step", 3, "Installing demucs (large download, please wait)...", 94)
            try:
                subprocess.run([sys.executable, "-m", "pip", "install", "demucs", "soundfile",
                                "torch<2.9", "torchaudio<2.9"],
                               check=True, capture_output=True, creationflags=flags)
                importlib.invalidate_caches()
                have = has_module("demucs")
            except Exception:
                pass
            if not have:
                why = "demucs could not be installed"
        self._check()

        if have:
            out_dir = os.path.join(wd, "sep")
            found = glob.glob(os.path.join(out_dir, "**", "no_vocals.*"), recursive=True)
            if not found:                       # the AI separation only needs to run once
                log_path = os.path.join(wd, "demucs.log")
                t0 = time.time()
                with open(log_path, "w") as log:
                    proc = subprocess.Popen(
                        [sys.executable, "-m", "demucs", "--two-stems=vocals", "-o", out_dir, src],
                        stdout=log, stderr=subprocess.STDOUT, creationflags=flags)
                    while proc.poll() is None:
                        if self.cancel_flag.is_set():
                            proc.terminate()
                            raise Cancelled()
                        self._post("step", 3, "Removing the original voice with AI "
                                              f"(can take a while)... {fmt_time(time.time() - t0)}",
                                   94)
                        time.sleep(1)
                found = glob.glob(os.path.join(out_dir, "**", "no_vocals.*"), recursive=True)
            if found:
                self.done_note = ""
                return found[0]
            why = "demucs failed to run"

        # basic method: silence the original sound whenever someone is speaking
        orig = [(sg.get("os", sg["start"]), sg.get("oe", sg["end"])) for sg in segs]
        if not orig:
            return src
        parts = [f"between(t,{max(a - 0.12, 0):.2f},{b + 0.12:.2f})" for a, b in orig]
        script = os.path.join(wd, "gate.txt")
        with open(script, "w") as f:
            f.write("volume='if(gte(" + "+".join(parts) + ",1),0,1)':eval=frame")
        bg = os.path.join(wd, "bg_basic.wav")
        run_ffmpeg(["-i", src, "-filter_script:a", script, "-ar", "44100", bg])
        self.done_note = ("  (" + (why + ". " if why else "") + "Basic voice removal was used: the "
                          "original sound is muted while people speak. Install demucs for the "
                          "best result.)")
        return bg

    # ---------------------------------------------- stage 1: listen + translate
    def _trim_and_analyze(self, video, trim, model_size, remember, engine, auto_voice=True):
        """Cut away the part of the video we do not need, then work only on the kept part."""
        if trim:
            start, end = trim
            tag = f"{fmt_time(start)}-{fmt_time(end) if end else 'end'}".replace(":", "-")
            base = os.path.splitext(os.path.basename(video))[0]
            out = os.path.join(os.path.dirname(os.path.abspath(video)), f"{base}_{tag}.mp4")
            try:                                          # keep the clip next to the original
                open(out, "ab").close()
            except OSError:
                out = os.path.join(self.workdir, f"{base}_{tag}.mp4")
            self._post("step", 0, f"Cutting the video to {fmt_time(start)} - "
                                  f"{fmt_time(end) if end else 'the end'} ...", 1)
            args = ["-ss", f"{start:.3f}", "-i", video]
            if end:
                args += ["-t", f"{end - start:.3f}"]
            args += ["-map", "0:v:0", "-map", "0:a:0?", "-c:v", "libx264", "-preset", "veryfast",
                     "-crf", "20", "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "192k", out]
            try:
                run_ffmpeg(args)
            except RuntimeError:
                raise RuntimeError("I could not cut the video. Check the start/end times.")
            self._check()
            self._post("trimmed", out)
            video = out
        self._analyze(video, model_size, remember, engine, auto_voice)

    def _analyze(self, video, model_size, remember, engine, auto_voice=True):
        import numpy as np
        from deep_translator import GoogleTranslator
        from faster_whisper import WhisperModel

        wd = self.workdir

        st = os.stat(video)
        key = hashlib.md5(f"{os.path.abspath(video)}|{st.st_size}|{int(st.st_mtime)}|"
                          f"{model_size}".encode()).hexdigest()[:16]
        cache_dir = os.path.join(os.path.expanduser("~"), ".khmer_dubber_cache")
        cache_file = os.path.join(cache_dir, key + ".json")
        segs, total = [], 0.0

        def save_cache():
            if not remember:
                return
            try:
                os.makedirs(cache_dir, exist_ok=True)
                with open(cache_file, "w", encoding="utf-8") as f:
                    json.dump({"total": total, "segs": segs}, f, ensure_ascii=False)
            except Exception:
                pass

        try:
            if not remember:
                raise FileNotFoundError
            with open(cache_file, encoding="utf-8") as f:
                c = json.load(f)
            segs, total = c["segs"], float(c["total"])
        except Exception:
            segs, total = [], 0.0

        # ================= step 0: listen =================
        if segs:
            self._post("step", 0, "Found saved results from an earlier run - skipping listening", 40)
            for i, sg in enumerate(segs):
                self._post("row", i, sg)
        else:
            self._post("step", 0, "Reading the audio from your video...", 2)
            wav16 = os.path.join(wd, "whisper16k.wav")
            try:
                run_ffmpeg(["-i", video, "-vn", "-af", "aresample=async=1:first_pts=0",
                            "-ac", "1", "-ar", "16000", wav16])
            except RuntimeError:
                raise RuntimeError("This video has no sound I can read.")
            with wave.open(wav16, "rb") as w:
                raw = w.readframes(w.getnframes())
            audio = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
            del raw
            total = len(audio) / 16000.0
            self._check()

            peak = float(np.max(np.abs(audio))) if audio.size else 0.0
            rms = float(np.sqrt(np.mean(audio ** 2))) if audio.size else 0.0
            level_db = 20 * math.log10(rms) if rms > 0 else -99.0
            if 0.001 < peak < 0.6:
                audio = np.clip(audio * min(0.9 / peak, 12.0), -1.0, 1.0).astype(np.float32)

            self._post("step", 0, f"Video length {fmt_time(total)}. Loading the speech model "
                                  "(the first time it downloads, please wait)...", 5)
            model = WhisperModel(model_size, device="cpu", compute_type="int8",
                                 cpu_threads=os.cpu_count() or 4)
            self._check()

            def listen(use_vad, label):
                kw = dict(language="zh", beam_size=(5 if model_size == "medium" else 1),
                          initial_prompt="以下是普通话的句子。", condition_on_previous_text=False)
                if use_vad:
                    kw.update(vad_filter=True,
                              vad_parameters=dict(threshold=0.3, min_silence_duration_ms=600))
                gen, info = model.transcribe(audio, **kw)
                dur_s = max(info.duration, 1)
                found = []
                t_start = time.time()
                for s in gen:
                    self._check()
                    text = s.text.strip()
                    if not text:
                        continue
                    if getattr(s, "no_speech_prob", 0) > 0.8 and getattr(s, "avg_logprob", 0) < -1:
                        continue
                    seg = {"start": s.start, "end": s.end, "zh": text, "km": "..."}
                    found.append(seg)
                    self._post("row", len(found) - 1, seg)
                    done_frac = min(s.end / dur_s, 1)
                    eta = ""
                    if done_frac > 0.03:
                        left = (time.time() - t_start) * (1 - done_frac) / done_frac
                        eta = f", about {fmt_time(left)} left"
                    self._post("step", 0, f"Listening{label}... {fmt_time(s.end)} of "
                                          f"{fmt_time(dur_s)}{eta}", 5 + 35 * done_frac)
                return found

            segs = listen(True, "")
            if not segs:
                self._post("step", 0, "Trying again with a more sensitive setting...", 6)
                segs = listen(False, " (sensitive mode)")
            if not segs:
                if level_db < -55:
                    why = "The audio in this video is almost silent."
                else:
                    why = ("The audio has sound, but no clear Chinese speech was found "
                           "(it may be music only, or another language).")
                raise RuntimeError(why + f"\n\nAudio loudness: {level_db:.0f} dB "
                                   "(speech is usually above -40 dB).\n"
                                   "Tip: try the 'Best (slower)' accuracy, or a video with clearer speech.")
            segs = merge_segments(segs)
            self._post("clear_rows")
            for i, sg in enumerate(segs):
                self._post("row", i, sg)
            del audio
            save_cache()

        for sg in segs:                         # remember where the Chinese speech really was
            sg.setdefault("os", sg["start"])
            sg.setdefault("oe", sg["end"])
        segs = split_lines(segs)                 # 2 sentences in one box -> 2 boxes

        # ---- auto male / female voice (from the pitch of the original speaker)
        if not auto_voice:
            for sg in segs:                         # undo voices chosen by an earlier auto run
                if sg.pop("auto_voice", False):
                    sg.pop("voice", None)
        else:
            need_g = [sg for sg in segs if not sg.get("voice")]
            if need_g:
                self._post("step", 0, "Checking who is speaking (male or female)...", 41)
                wav16 = os.path.join(wd, "whisper16k.wav")
                try:
                    if not os.path.exists(wav16):
                        run_ffmpeg(["-i", video, "-vn", "-ac", "1", "-ar", "16000", wav16])
                    with wave.open(wav16, "rb") as w:
                        raw = w.readframes(w.getnframes())
                    voice_audio = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
                    del raw
                    last = None
                    for sg in segs:
                        if sg.get("voice"):
                            continue
                        self._check()
                        g = detect_voice(voice_audio, sg.get("os", sg["start"]),
                                         sg.get("oe", sg["end"])) or last
                        if g:
                            sg["voice"] = g
                            sg["auto_voice"] = True
                            last = g
                    del voice_audio
                    save_cache()
                except Cancelled:
                    raise
                except Exception:
                    pass                            # detection is a bonus - never block the dub

        # ================= step 1: translate =================
        todo = [i for i, sg in enumerate(segs) if sg["km"] in ("...", "")]
        if todo:
            tr = GoogleTranslator(source="zh-CN", target="km")

            def translate_text(text):
                try:
                    out = google_fast(text)
                    if out.strip():
                        return out
                except Exception:
                    pass
                return tr.translate(text)

            def with_retry(fn, pct):
                delay = 3
                for attempt in range(6):
                    self._check()
                    try:
                        return fn()
                    except Exception as e:
                        if attempt == 5:
                            raise
                        busy = "toomany" in type(e).__name__.lower() or "too many" in str(e).lower()
                        note = "Google asked me to slow down" if busy else "Translation hiccup"
                        for k in range(delay, 0, -1):
                            self._check()
                            self._post("step", 1, f"{note} - waiting {k}s, then trying again", pct)
                            time.sleep(1)
                        delay = min(delay * 2, 20)

            ms_ok = [engine == "microsoft"]

            chunks, cur, size = [], [], 0
            for i in todo:
                n = len(segs[i]["zh"])
                if cur and (size + n > 3000 or len(cur) >= 30):
                    chunks.append(cur)
                    cur, size = [], 0
                cur.append(i)
                size += n + 1
            if cur:
                chunks.append(cur)

            for ci, idxs in enumerate(chunks):
                pct = 40 + 20 * ci / len(chunks)
                self._post("step", 1, f"Translating part {ci + 1} of {len(chunks)}", pct)
                texts = [segs[i]["zh"].replace("\n", " ") for i in idxs]
                parts = None
                if ms_ok[0]:
                    try:
                        self._check()
                        parts = ms_translate(texts)
                    except Cancelled:
                        raise
                    except Exception:
                        ms_ok[0] = False
                        self._post("step", 1, "Microsoft translator not available - "
                                              "using Google instead", pct)
                if parts is None:
                    out = with_retry(lambda: translate_text("\n".join(texts)), pct) or ""
                    parts = [x.strip() for x in out.split("\n")]
                    if len(parts) != len(idxs):
                        parts = []
                        for t in texts:
                            parts.append(with_retry(lambda t=t: translate_text(t), pct) or t)
                            time.sleep(0.3)
                for i, km in zip(idxs, parts):
                    segs[i]["km"] = km or segs[i]["zh"]
                    self._post("update_km", i, segs[i]["km"])
                save_cache()
        else:
            for i, sg in enumerate(segs):
                self._post("update_km", i, sg["km"])

        segs = split_lines(segs)                 # 3 lines in one box -> 3 boxes
        self._post("analyzed", segs, total)

    # ---------------------------------------------- stage 2: voice + video
    def _render(self, o):
        import edge_tts
        from concurrent.futures import ThreadPoolExecutor

        wd = self.workdir
        SR = 24000
        segs, total, video = o["segs"], o["total"], o["video"]
        shift = o["shift"]
        orig_pct = o["orig_pct"]

        # ---- step 2: Khmer voice (only lines that are new or changed are made again)
        keys, need = [], {}
        for sg in segs:
            text = (sg.get("km") or "").strip()
            if not text or text == "..." or sg.get("mute"):
                keys.append(None)
                continue
            vid = VOICES.get(sg.get("voice") or "", o["voice"])
            k = hashlib.md5((vid + "|" + text).encode("utf-8")).hexdigest()[:16]
            keys.append(k)
            need[k] = (text, vid)

        def p(k, ext):
            return os.path.join(wd, f"c_{k}.{ext}")

        todo = [k for k in need if not os.path.exists(p(k, "wav"))
                and not os.path.exists(p(k, "none")) and not os.path.exists(p(k, "mp3"))]
        done_count = [0]
        self._post("step", 2, f"Voice 0 of {len(todo)}" if todo else
                   "All voices are already made - reusing them", 60)

        async def synth_all():
            sem = asyncio.Semaphore(6)

            async def one(k):
                text, vid = need[k]
                async with sem:
                    for attempt in range(3):
                        if self.cancel_flag.is_set():
                            return
                        try:
                            await edge_tts.Communicate(text, vid).save(p(k, "mp3"))
                            break
                        except Exception as e:
                            if type(e).__name__ == "NoAudioReceived":
                                open(p(k, "none"), "w").close()
                                return
                            if attempt == 2:
                                raise
                            await asyncio.sleep(1 + attempt)
                done_count[0] += 1
                self._post("step", 2, f"Voice {done_count[0]} of {len(todo)}",
                           60 + 28 * done_count[0] / max(len(todo), 1))

            await asyncio.gather(*(one(k) for k in todo))

        if todo:
            asyncio.run(synth_all())
        self._check()

        # ---- step 3: build the Khmer track and the video
        self._post("step", 3, "Fitting the Khmer voice to the video timing...", 89)

        def trim(k):
            if not os.path.exists(p(k, "mp3")) or os.path.exists(p(k, "wav")):
                return
            self._check()
            tmp = p(k, "tmp.wav")
            cut = ("silenceremove=start_periods=1:start_threshold=-50dB:detection=peak,areverse,"
                   "silenceremove=start_periods=1:start_threshold=-50dB:detection=peak,areverse")
            run_ffmpeg(["-i", p(k, "mp3"), "-af", cut, "-ar", str(SR), "-ac", "1", tmp])
            with wave.open(tmp, "rb") as w:
                dur = w.getnframes() / SR
            if dur >= 0.06:
                os.replace(tmp, p(k, "wav"))
            else:
                os.remove(tmp)
                open(p(k, "none"), "w").close()

        to_trim = [k for k in need if not os.path.exists(p(k, "wav"))
                   and not os.path.exists(p(k, "none"))]
        with ThreadPoolExecutor(max_workers=4) as ex:
            list(ex.map(trim, to_trim))

        def dur_of(k):
            if not k or not os.path.exists(p(k, "wav")):
                return None
            with wave.open(p(k, "wav"), "rb") as w:
                return w.getnframes() / SR

        durs = [dur_of(k) for k in keys]
        plan = plan_voice(segs, durs, shift)

        def stretch(item):
            i, start, ratio = item
            self._check()
            path = p(keys[i], "wav")
            vol = float(segs[i].get("vol", 1.0))
            filt = []
            if abs(ratio - 1) > 0.03:
                filt.append(tempo_filter(ratio))
            if abs(vol - 1) > 0.02:
                filt.append(f"volume={vol:.2f}")
                if vol > 1:
                    filt.append("alimiter=limit=0.95")
            if filt:
                outp = os.path.join(wd, f"r{i}.wav")
                run_ffmpeg(["-i", path, "-filter:a", ",".join(filt), outp])
                path = outp
            return path, start

        with ThreadPoolExecutor(max_workers=4) as ex:
            placed = list(ex.map(stretch, plan))

        self._post("step", 3, "Writing the Khmer voice track...", 92)
        dub_path = os.path.join(wd, "dub.wav")
        total_frames = int(total * SR) + SR
        with wave.open(dub_path, "wb") as out_w:
            out_w.setnchannels(1)
            out_w.setsampwidth(2)
            out_w.setframerate(SR)
            written = 0

            def silence(n):
                while n > 0:
                    kk = min(n, SR * 10)
                    out_w.writeframes(b"\x00\x00" * kk)
                    n -= kk

            for path, start in placed:
                with wave.open(path, "rb") as w:
                    data = w.readframes(w.getnframes())
                st = max(int(start * SR), written)
                if st >= total_frames:
                    break
                silence(st - written)
                out_w.writeframes(data)
                written = st + len(data) // 2
            silence(max(total_frames - written, 0))

        out = o["out"]
        self._post("step", 3, "Building the final video (long videos take a few minutes)...", 95)

        bg_path = None
        if o["remove_voice"]:
            if orig_pct <= 0:
                orig_pct = 60
            bg_path = self._background_only(video, wd, o["install_demucs"], segs)
            self._check()
            self._post("step", 3, "Building the final video (long videos take a few minutes)...", 95)

        src_a = "[2:a]" if bg_path else "[0:a]"
        fmt = "aformat=sample_rates=44100:channel_layouts=stereo"
        if orig_pct <= 0:
            fc = f"[1:a]{fmt}[a]"
        else:
            fc = (f"{src_a}{fmt},volume={orig_pct / 100:.3f}[o];"
                  f"[1:a]{fmt}[d];"
                  "[o][d]amix=inputs=2:duration=first:dropout_transition=0,"
                  "volume=2,alimiter=limit=0.95[a]")
        mux = ["-i", video, "-i", dub_path] + (["-i", bg_path] if bg_path else []) + [
               "-filter_complex", fc,
               "-map", "0:v:0", "-map", "[a]"]
        tail = ["-c:a", "aac", "-b:a", "192k", "-shortest", out]

        burned = False
        if o["burn"]:
            self._post("step", 3, "Burning the Khmer subtitles into the video...", 96)
            with open(os.path.join(wd, "subs.srt"), "w", encoding="utf-8") as f:
                f.write(to_srt(segs))
            style = (f"FontName={KHMER_FONT},FontSize=18,PrimaryColour=&H00FFFFFF,"
                     "OutlineColour=&H00000000,BorderStyle=1,Outline=2,Shadow=0,"
                     "Alignment=2,MarginV=24")
            try:
                run_ffmpeg(mux + ["-filter:v", f"subtitles=subs.srt:force_style='{style}'",
                                  "-c:v", "libx264", "-preset", "fast", "-crf", "20",
                                  "-pix_fmt", "yuv420p"] + tail, cwd=wd)
                burned = True
            except RuntimeError:
                self.done_note += ("  (Subtitles could not be burned in because this FFmpeg has "
                                   "no subtitle support. Use 'Export .srt' instead.)")
        if not burned:
            try:
                run_ffmpeg(mux + ["-c:v", "copy"] + tail)
            except RuntimeError:
                run_ffmpeg(mux + ["-c:v", "libx264", "-preset", "fast", "-crf", "20",
                                  "-pix_fmt", "yuv420p"] + tail)
        self._post("done", out)



# ======================================================================= web server

import copy
import io
import json
import mimetypes
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import uuid

from flask import Flask, Response, jsonify, make_response, render_template_string, request, send_file

import hashlib

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = None

BOOT = int(time.time())
SESSIONS = {}
LOCK = threading.Lock()


class Session:
    def __init__(self):
        self.workdir = tempfile.mkdtemp(prefix="khmer_dub_")
        self.msgs = queue.Queue()
        self.pipe = Pipeline(self.workdir, self.post)
        self.video_path = None
        self.dubbed_path = None
        self.project_path = None
        self.busy = False
        self.render_no = 0
        self.t0 = time.time()
        self.settings = {}
        self.touched = time.time()

    def post(self, kind, *a):
        self.msgs.put((kind, a))


def get_session():
    sid = request.cookies.get("sid")
    with LOCK:
        s = SESSIONS.get(sid)
        if s is None:
            sid = uuid.uuid4().hex
            s = SESSIONS[sid] = Session()
        s.touched = time.time()
        request.sid = sid
        return s


@app.after_request
def set_cookie(resp):
    sid = getattr(request, "sid", None)
    if sid and request.cookies.get("sid") != sid:
        resp.set_cookie("sid", sid, httponly=True, samesite="Lax")
    resp.headers["Cache-Control"] = "no-store"
    return resp


def clean_stale(wd):
    """New video -> forget the separated-voice copies of the previous one."""
    for name in ("orig44.wav", "bg_basic.wav", "whisper16k.wav"):
        try:
            os.remove(os.path.join(wd, name))
        except OSError:
            pass
    shutil.rmtree(os.path.join(wd, "sep"), ignore_errors=True)



INDEX_HTML = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#0a0a0c">
<title>Khmer Dubber Editor</title>
<link rel="stylesheet" href="/static/style.css?v=__V__">
</head>
<body>
<div id="app">

<!-- ================= side bar ================= -->
<aside id="side">
  <button id="sideToggle" title="Menu">&#9776;</button>
  <div id="sideBody">
    <div class="brand"><h1>Khmer Dubber</h1><p>CHINESE VIDEO &nbsp;&rarr;&nbsp; KHMER VOICE</p></div>

    <div class="heading"><i></i><span>S E T T I N G S</span><b></b></div>
    <div class="group"><div class="cap">KHMER VOICE (DEFAULT)</div><div class="seg" id="voiceSeg"></div></div>
    <div class="group sep"><div class="cap">ORIGINAL SOUND</div>
      <div class="sl"><input type="range" id="soundSl" min="0" max="100" step="5" value="20"><span id="soundVal">20%</span></div></div>
    <div class="group sep"><div class="cap">KHMER VOICE TIMING (ALL)</div>
      <div class="sl"><input type="range" id="shiftSl" min="-2" max="2" step="0.1" value="0"><span id="shiftVal">on time</span></div></div>
    <div class="group sep"><div class="cap">TRANSLATOR</div><div class="seg" id="engineSeg"></div></div>
    <div class="group sep"><div class="cap">ACCURACY</div><div class="seg" id="accSeg"></div></div>
    <div class="group sep" id="checks"></div>

    <div class="heading"><i></i><span>F I L E</span><b></b></div>
    <button class="primary" id="sbRender">Make dubbed video</button>
    <div id="fileItems"></div>
    <div class="heading"><i></i><span>E D I T</span><b></b></div>
    <div id="editItems"></div>
    <div class="ver">Khmer Dubber Editor v13</div>
  </div>
</aside>
<div id="sideVeil"></div>
<div class="vline"></div>

<!-- ================= page ================= -->
<main id="page">
  <div id="warn" class="warn" hidden>
    <span class="bang">!</span><div id="warnText"></div>
    <button class="btn accent" id="installBtn">Install now</button>
  </div>

  <div class="head">
    <button class="btn" id="menuBtn" aria-label="Menu">&#9776;</button>
    <div class="headTxt">
      <div class="titleLine"><span class="title">Khmer Dubber</span><span class="muted"> &nbsp;Editor v13</span></div>
      <div class="muted" id="fileLbl">Turn a Chinese video into a Khmer-dubbed video, then edit it</div>
    </div>
    <div class="headBtns">
      <button class="btn" id="chooseBtn">Choose video...</button>
      <button class="btn accent" id="saveBtn">Save video...</button>
      <button class="btn" id="folderBtn" >Open folder</button>
    </div>
  </div>
  <div class="rule"></div>

  <div class="cols">
    <section class="left">
      <div class="lh"><span class="h2">Preview</span>
        <span class="snd"><span class="muted">Audio</span>
          <button class="segbtn" id="modeDub">Khmer voice</button><button class="segbtn on" id="modeOrig">Original</button></span></div>
      <div id="videoFrame">
        <video id="video" playsinline preload="auto"></video>
        <div id="drop">
          <svg width="88" height="88" viewBox="0 0 88 88"><circle id="dropCircle" cx="44" cy="44" r="40" fill="none" stroke="#c9a45c" stroke-dasharray="2 5"/><path id="dropPlus" d="M44 27V61M27 44H61" stroke="#c9a45c" stroke-width="2" stroke-linecap="round"/></svg>
          <div class="dropTitle" id="dropTitle">Choose a video</div>
          <div class="dropSub" id="dropSub">Click here, or drag a video file onto this window<br>MP4 &nbsp;&middot;&nbsp; MOV &nbsp;&middot;&nbsp; MKV &nbsp;&middot;&nbsp; AVI &nbsp;&middot;&nbsp; WEBM</div>
        </div>
      </div>
      <div id="caption"></div>
      <div class="ctrl">
        <button class="btn" id="playBtn" style="width:70px">Play</button>
        <input type="range" id="seek" min="0" max="1000" value="0">
        <span class="muted" id="timeLbl">00:00 / 00:00</span>
      </div>
    </section>

    <section class="right">
      <div class="lh"><span class="h2">Lines</span><span class="muted">click to edit - double-click to jump</span></div>
      <div class="card" id="treeBox"><table id="tree"><thead><tr><th style="width:60px">TIME</th><th>CHINESE</th><th>KHMER</th></tr></thead><tbody></tbody></table></div>

      <div class="card" id="editPanel">
        <div class="cap" id="panelTitle">EDIT LINE &nbsp;-&nbsp; select a block on the timeline</div>
        <div class="pgrid">
          <label class="top">Chinese</label><textarea id="tZh" rows="2" class="span3"></textarea>
          <label class="top">Khmer</label><textarea id="tKm" rows="3" class="span3 km"></textarea>
          <label>Start (s)</label><input type="number" id="fStart" step="0.1" min="0">
          <label class="r">End (s)</label><input type="number" id="fEnd" step="0.1" min="0">
          <label>Voice</label><select id="cbVoice"></select>
          <label class="r">Speed</label><select id="cbSpeed"></select>
          <label>Volume</label><div class="sl span3"><input type="range" id="fVol" min="0" max="200" step="5" value="100"><span id="volLbl">100%</span></div>
        </div>
        <div class="tgRow" id="panelToggles"></div>
        <div class="pbtns"><button class="btn tool" id="retrBtn">Re-translate</button><button class="btn tool" id="hearBtn">Hear this line</button></div>
      </div>
    </section>
  </div>

  <div class="card tlCard">
    <div class="tlbar">
      <button class="btn tool" id="undoBtn">Undo</button><button class="btn tool" id="redoBtn">Redo</button><span class="muted">|</span>
      <button class="btn tool" id="splitBtn">Split (S)</button><button class="btn tool" id="mergeBtn">Merge next</button>
      <button class="btn tool" id="delBtn">Delete (Del)</button><button class="btn tool" id="sentBtn">Split lines</button>
      <button class="btn tool" id="addBtn">Add line</button><span class="muted">|</span>
      <button class="btn tool" id="srtBtn">Export .srt</button>
      <span class="grow"></span>
      <span class="muted">Zoom</span><input type="range" id="zoomSl" min="5" max="200" step="1" value="40" style="width:140px"><button class="btn tool" id="fitBtn">Fit</button>
    </div>
    <div id="tlWrap"><canvas id="tl" height="138"></canvas></div>
  </div>

  <div class="card prog">
    <div class="steps" id="steps"></div>
    <div class="bar"><div id="barFill"></div></div>
    <div class="foot">
      <span class="muted grow" id="progDetail">Choose a video to start. Nothing is saved until you press 'Save video...'.</span>
      <button class="btn" id="cancelBtn">Cancel</button>
      <button class="btn accent" id="renderBtn">Make dubbed video</button>
    </div>
  </div>
</main>
</div>

<input type="file" id="fileVideo" accept="video/*,.mkv,.mov,.avi,.webm,.mp4" hidden>
<input type="file" id="fileProj" accept=".khdub" hidden>
<input type="file" id="fileProjVideo" accept="video/*,.mkv,.mov,.avi,.webm,.mp4" hidden>
<audio id="pvAudio"></audio>
<div id="ctx" class="ctx" hidden></div>
<div id="modal" hidden><div class="mbox"><h3 id="mTitle"></h3><div id="mBody"></div><input id="mInput" hidden><div class="mbtns" id="mBtns"></div></div></div>
<div id="dragVeil" hidden>Drop the video (or a .khdub project) here</div>

<script src="/static/app.js?v=__V__"></script>
</body>
</html>
'''

STYLE_CSS = r''':root{
  --bg:#0a0a0c;--panel:#121215;--panel2:#1a1a1f;--alt:#0f0f12;--line:#26262c;--hover:#24232a;
  --fg:#f3efe6;--muted:#8d887c;--accent:#c9a45c;--accent-h:#b58f47;--accent-l:#e6cf9a;--accent-fg:#15110a;
  --ok:#7fd6a4;--video:#050506;--warn-bg:#211b0d;--warn-line:#5a4a22;
  --ui:"Segoe UI Variable Display","Segoe UI Variable Text","Segoe UI","SF Pro Display","Helvetica Neue","Noto Sans","DejaVu Sans",sans-serif;
  --km:"Leelawadee UI","Noto Sans Khmer","Khmer OS","Khmer UI",sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--bg);color:var(--fg);font:10pt var(--ui)}
#app{display:flex;height:100vh}
button{font-family:inherit}
.muted{color:var(--muted)}.grow{flex:1}
.cap{color:var(--accent);font-size:8pt;font-weight:700;margin-bottom:4px}
.h2{font-size:12pt;font-weight:700;color:var(--accent-l)}

/* side bar */
#side{width:300px;min-width:44px;background:var(--panel);overflow:hidden;transition:width .24s cubic-bezier(.2,.8,.2,1);flex:none;display:flex;flex-direction:column}
#side.closed{width:44px}
#side.closed #sideBody{display:none}
#sideToggle{background:none;border:0;color:var(--fg);font-size:14pt;cursor:pointer;align-self:flex-start;padding:8px 0 4px 12px}
#sideBody{overflow-y:auto;flex:1;padding-bottom:10px;scrollbar-width:thin;scrollbar-color:#2c2b31 var(--bg)}
.vline{width:1px;background:var(--line);flex:none}
.brand{padding:2px 18px 0}.brand h1{margin:0;font-size:17pt}.brand p{margin:1px 0 0;color:var(--muted);font-size:9pt}
.heading{display:flex;align-items:center;margin:20px 18px 8px}
.heading i{width:2px;height:12px;background:var(--accent);margin-right:8px}
.heading span{color:var(--accent);font-size:8pt;font-weight:700;white-space:nowrap}
.heading b{flex:1;height:1px;background:var(--line);margin-left:10px}
.group{padding:0 18px;margin-top:10px}
.group.sep{border-top:1px solid var(--line);margin:12px 18px 0;padding:10px 0 0}
.seg{display:flex;gap:2px;flex-wrap:wrap}
.segbtn{background:var(--panel2);color:var(--muted);border:0;padding:7px 14px;cursor:pointer;font-size:10pt}
.segbtn:hover{background:var(--hover);color:var(--fg)}
.segbtn.on{background:var(--accent);color:var(--accent-fg)}
.segbtn.on:hover{background:var(--accent-h)}
.sl{display:flex;align-items:center;gap:10px}
.sl span{min-width:70px;font-size:10pt}
button.primary{display:block;width:calc(100% - 36px);margin:0 18px 8px;background:var(--accent);color:var(--accent-fg);border:0;padding:12px;font-size:11pt;font-weight:700;cursor:pointer}
button.primary:hover:not(:disabled){background:var(--accent-h)}
button.primary:disabled{background:var(--panel2);color:#6f6850;cursor:default}
.item{display:flex}.item i{width:3px;background:var(--panel)}
.item button{flex:1;text-align:left;background:var(--panel);color:var(--fg);border:0;padding:7px 15px;font-size:11pt;cursor:pointer}
.item:hover:not(.dis) i{background:var(--accent)}.item:hover:not(.dis) button{background:var(--hover)}
.item.dis button{color:#5b6277;cursor:default}
.ver{color:#4d4a42;font-size:8pt;padding:20px 18px 14px}

/* toggles */
.tg{display:flex;align-items:center;cursor:pointer;margin-bottom:9px;user-select:none}
.tg .lbl{flex:1;color:#a8a396;transition:color .18s}
.tg.on .lbl{color:var(--fg)}
.tg .pill{flex:none;width:42px;height:24px;border-radius:12px;border:1px solid #3a3a42;background:#1f1f25;position:relative;transition:all .18s}
.tg .pill::after{content:"";position:absolute;top:4px;left:5px;width:14px;height:14px;border-radius:50%;background:#8d887c;transition:all .18s}
.tg.on .pill{background:var(--accent);border-color:var(--accent-l)}
.tg.on .pill::after{left:23px;background:var(--accent-fg)}
.tg:hover .pill{border-color:var(--accent-l)}
.tg.inl{margin:0 22px 0 0;flex:none}.tg.inl .pill{order:-1;margin-right:10px;flex:none}.tg.inl .lbl{flex:none;white-space:nowrap}

/* range sliders */
input[type=range]{-webkit-appearance:none;appearance:none;background:linear-gradient(to right,var(--accent) var(--p,0%),#2a2a31 var(--p,0%)) center/100% 3px no-repeat;border-radius:2px;height:22px;cursor:pointer;flex:1;min-width:0;margin:0}
input[type=range]::-webkit-slider-runnable-track{height:3px;background:transparent}
input[type=range]::-webkit-slider-thumb{-webkit-appearance:none;width:12px;height:12px;border-radius:50%;background:var(--accent-l);border:1px solid var(--accent);margin-top:-5px}
input[type=range]:hover::-webkit-slider-thumb{box-shadow:0 0 0 4px #2b2515;width:14px;height:14px;margin-top:-6px}
input[type=range]::-moz-range-track{height:3px;background:transparent}
input[type=range]::-moz-range-thumb{width:12px;height:12px;border-radius:50%;background:var(--accent-l);border:1px solid var(--accent)}
input[type=range]:disabled{opacity:.4;cursor:default}

/* page */
#page{flex:1;min-width:0;height:100vh;padding:14px 24px 40px;overflow-y:auto;display:flex;flex-direction:column;scrollbar-width:thin;scrollbar-color:#2c2b31 var(--bg)}
.warn{flex:none;display:flex;align-items:center;background:var(--warn-bg);border:1px solid var(--warn-line);margin-bottom:10px;color:var(--accent-l)}
.warn[hidden]{display:none}
.bang{background:var(--accent);color:var(--accent-fg);font-weight:700;width:24px;text-align:center;margin:8px 0 8px 10px}
#warnText{flex:1;padding:8px 10px;white-space:pre-line}
.warn .btn{margin:8px 10px}
.head{flex:none;display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;gap:12px;flex-wrap:wrap}
.title{font-size:22pt;font-weight:700;line-height:1.1}
.headBtns{display:flex;gap:8px;flex-wrap:wrap}
.rule{height:1px;background:var(--line);margin-bottom:10px;flex:none}
.btn{background:var(--panel2);color:var(--fg);border:0;padding:9px 18px;cursor:pointer;font-size:10pt}
.btn:hover:not(:disabled){background:var(--hover)}
.btn:active:not(:disabled){background:var(--line)}
.btn:disabled{background:var(--panel);color:#5a5750;cursor:default}
.btn.accent{background:var(--accent);color:var(--accent-fg);font-weight:700;padding:10px 20px}
.btn.accent:hover:not(:disabled){background:var(--accent-h)}
.btn.accent:disabled{background:#2a2519;color:#6f6850}
.btn.tool{padding:6px 12px}
.cols{position:relative;display:grid;grid-template-columns:minmax(0,3fr) minmax(0,2fr);grid-auto-rows:minmax(500px,auto);gap:24px;flex:1 0 auto}
.left,.right{min-width:0;min-height:0;display:flex;flex-direction:column}
.lh{flex:none;display:flex;justify-content:space-between;align-items:center;margin-bottom:6px}
.snd{display:flex;align-items:center;gap:8px}
#videoFrame{position:relative;background:var(--video);border:1px solid var(--line);flex:1 1 0;min-height:200px;overflow:hidden}
#video{position:absolute;inset:0;width:100%;height:100%;display:block;object-fit:contain;background:var(--video)}
#drop{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);text-align:center;cursor:pointer}
#drop[hidden]{display:none}
.dropTitle{color:var(--accent-l);font-size:17pt;font-weight:700;margin:14px 0 4px}
.dropSub{color:var(--muted);line-height:1.5}
#drop:hover circle,#drop:hover path{stroke:var(--accent-l)}
#caption{height:2.4em;flex:none;display:flex;align-items:center;justify-content:center;margin-top:6px;color:var(--accent-l);font:14pt var(--km);text-align:center;line-height:1.35;overflow:hidden}
.ctrl{flex:none;display:flex;align-items:center;gap:12px;margin-top:2px}
#timeLbl{width:110px;text-align:right}

.card{background:var(--panel);border:1px solid var(--line)}
#treeBox{flex:1 1 0;min-height:90px;overflow-y:auto;scrollbar-width:thin;scrollbar-color:#2c2b31 var(--panel)}
#tree{width:100%;border-collapse:collapse;table-layout:fixed;font-family:var(--km)}
#tree th{position:sticky;top:0;background:var(--panel2);color:var(--accent);text-align:left;padding:8px 10px;font:700 9pt var(--ui)}
#tree td{padding:6px 10px;height:34px;overflow:hidden;white-space:nowrap;text-overflow:ellipsis;cursor:pointer}
#tree tr.odd td{background:var(--alt)}#tree tr.even td{background:var(--panel)}
#tree tr.sel td{background:#2d2818;color:var(--accent-l)}
#editPanel{margin-top:10px;padding:12px 14px 12px;flex:none}
.pgrid{margin-top:10px;display:grid;grid-template-columns:auto 1fr auto 1fr;gap:6px 8px;align-items:center}
.pgrid label{color:var(--muted)}
.pgrid label.top{align-self:start;padding-top:7px}
#panelTitle{margin:0;letter-spacing:.3px;line-height:1.2}.pgrid label.r{padding-left:10px}
.span3{grid-column:2 / 5}
textarea,input[type=number],select,#mInput{background:var(--panel2);color:var(--fg);border:1px solid var(--line);padding:6px 8px;font:10pt var(--ui);width:100%;outline:none}
textarea.km{font:12pt var(--km)}
textarea:focus,input[type=number]:focus,select:focus,#mInput:focus{border-color:var(--accent)}
textarea{resize:vertical}
textarea:disabled,input:disabled,select:disabled{opacity:.5}
select option{background:var(--panel2)}
.tgRow{display:flex;align-items:center;margin:10px 0 8px;flex-wrap:wrap}
.pbtns{display:flex;gap:6px;margin-top:6px}.pbtns .btn:disabled{background:var(--panel2);color:#5a5750}

.tlCard{margin-top:10px;padding:8px 12px;flex:none}
.tlbar{display:flex;align-items:center;gap:4px;margin-bottom:6px;flex-wrap:wrap}
#tlWrap{overflow-x:auto;border:1px solid var(--line);background:var(--video);scrollbar-width:thin;scrollbar-color:#2c2b31 var(--bg)}
#tl{display:block}
.prog{margin-top:10px;padding:8px 16px;flex:none}
.steps{display:grid;grid-template-columns:repeat(4,1fr)}
.steps div{color:var(--muted)}
.bar{height:4px;background:var(--panel2);margin:8px 0 6px}
#barFill{height:100%;width:0;background:var(--accent);transition:width .2s}
.foot{display:flex;align-items:center;gap:8px}

/* menus / modal */
.ctx{position:fixed;background:var(--panel2);border:1px solid var(--line);z-index:50;min-width:190px}
.ctx[hidden]{display:none}
.ctx div{padding:6px 16px;cursor:pointer}.ctx div:hover{background:var(--accent);color:var(--accent-fg)}
.ctx hr{border:0;border-top:1px solid var(--line);margin:3px 0}
#modal{position:fixed;inset:0;background:rgba(0,0,0,.6);display:flex;align-items:center;justify-content:center;z-index:100}
#modal[hidden]{display:none}
.mbox{background:var(--panel);border:1px solid var(--line);padding:20px 24px;max-width:520px;width:90%}
.mbox h3{margin:0 0 10px;color:var(--accent-l)}
#mBody{white-space:pre-line;margin-bottom:12px;line-height:1.45}
.mbtns{display:flex;justify-content:flex-end;gap:8px;margin-top:14px}
#mInput{margin-top:4px}
#dragVeil{position:fixed;inset:0;background:rgba(10,10,12,.88);border:3px dashed var(--accent);color:var(--accent-l);display:flex;align-items:center;justify-content:center;font-size:20pt;z-index:200;pointer-events:none}
#dragVeil[hidden]{display:none}


.pgrid input[type=number],.pgrid select{min-width:0}
textarea#tZh{height:44px}textarea#tKm{height:62px}
@media(max-height:800px){#editPanel .pgrid{gap:4px 8px}#caption{height:2.2em;font-size:12pt}}

/* narrow window: stack everything so nothing overlaps */
#page.narrow .cols{display:flex;flex-direction:column;flex:none;min-height:0;gap:16px}
#page.narrow .left,#page.narrow .right{flex:none}
#page.narrow #videoFrame{flex:none;height:min(60vh,64vw);min-height:240px}
#page.narrow #treeBox{flex:none;height:220px}
#page.narrow .steps{grid-template-columns:repeat(2,1fr);row-gap:4px}
#page.narrow .foot{flex-wrap:wrap}
#page.narrow .foot .grow{flex-basis:100%}
.steps div{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.card,.tlCard,.prog{position:relative}

/* ================= responsive upgrade: laptop + tablet + phone ================= */
html,body{overscroll-behavior-y:none;-webkit-text-size-adjust:100%}
#app{height:100vh;height:100dvh}
#page{height:100vh;height:100dvh}
button,.segbtn,.btn,.tg{touch-action:manipulation;-webkit-tap-highlight-color:transparent}
#menuBtn{display:none;font-size:15pt;line-height:1;padding:8px 14px}
#sideVeil{display:none}
#tl{touch-action:none;-webkit-user-select:none;user-select:none}
#tlWrap{overscroll-behavior-x:contain}
.mbox{max-height:88vh;max-height:88dvh;overflow-y:auto}
.mbtns{flex-wrap:wrap}
.ctx{max-width:92vw}
.warn{flex-wrap:wrap}

/* laptops (13-15 inch) */
@media(max-width:1366px){
  #side{width:262px}
  #page{padding:12px 18px 32px}
  .cols{gap:18px}
  .title{font-size:19pt}
  .brand h1{font-size:15pt}
}
@media(max-width:1100px){
  #side{width:300px}
  #page{padding:14px 28px 32px}
  .cols{grid-template-columns:minmax(0,.9fr) minmax(0,1fr);gap:24px}
  .btn{padding:8px 14px}
  .btn.accent{padding:9px 16px}
  .tlbar{gap:3px}
}
@media(max-height:720px) and (min-width:761px){
  .head{margin-bottom:4px}
  .title{font-size:16pt}
  #caption{height:2em;font-size:11pt}
  textarea#tZh{height:38px}textarea#tKm{height:50px}
}

/* touch screens: big tap targets, no iOS zoom on focus */
@media(pointer:coarse){
  .btn,.segbtn{min-height:42px}
  .btn.tool{min-height:38px;padding:8px 14px}
  .item button{padding:13px 15px}
  .ctx div{padding:13px 20px}
  input[type=range]{height:40px}
  input[type=range]::-webkit-slider-thumb{width:24px;height:24px;margin-top:-10px}
  input[type=range]::-moz-range-thumb{width:24px;height:24px}
  textarea,input[type=number],select,#mInput{font-size:16px;min-height:42px}
  textarea.km{font-size:16px}
  textarea#tZh{height:64px}textarea#tKm{height:88px}
  #tree td{height:46px}
  #tree{-webkit-touch-callout:none;-webkit-user-select:none;user-select:none}
  .tg .pill{width:48px;height:28px;border-radius:14px}
  .tg .pill::after{top:5px;left:6px;width:16px;height:16px}
  .tg.on .pill::after{left:27px}
  .tg{min-height:40px}
  #tlWrap{-webkit-overflow-scrolling:touch}
}

/* tablets / phones */
#side.open + #sideVeil{opacity:1;pointer-events:auto}
@media(max-width:760px){
  html,body{font-size:11pt}
  #app{display:block}
  #side,#side.closed{position:fixed;z-index:80;top:0;bottom:0;left:0;width:min(88vw,330px);min-width:0;
    transform:translateX(-104%);transition:transform .26s cubic-bezier(.2,.8,.2,1);
    padding-top:env(safe-area-inset-top);padding-bottom:env(safe-area-inset-bottom)}
  #side.open{transform:none;box-shadow:8px 0 40px rgba(0,0,0,.7)}
  #side.closed #sideBody{display:block}
  #sideVeil{display:block;position:fixed;inset:0;z-index:70;background:rgba(0,0,0,.6);opacity:0;pointer-events:none;transition:opacity .2s}
  .vline{display:none}
  #page{width:100%;padding:calc(10px + env(safe-area-inset-top)) calc(12px + env(safe-area-inset-right)) calc(20px + env(safe-area-inset-bottom)) calc(12px + env(safe-area-inset-left))}
  #menuBtn{display:inline-block;flex:none}
  .head{flex-wrap:wrap;gap:8px;align-items:center}
  .headTxt{flex:1;min-width:0}
  .title{font-size:16pt}
  #fileLbl{font-size:9pt;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .headBtns{width:100%;display:grid;grid-template-columns:1fr 1fr;gap:8px}
  .headBtns .btn{padding:10px 8px;width:100%}
  #folderBtn{display:none}
  .headBtns .btn:nth-child(2){grid-column:auto}
  .lh .muted{display:none}
  #page.narrow #videoFrame{height:min(56vw,46dvh);min-height:170px}
  #page.narrow #videoFrame.tall{height:min(78dvh,108vw);min-height:260px}
  #page.narrow #treeBox{height:240px}
  #page.narrow .cols{gap:12px}
  #caption{font-size:12pt;height:2.7em}
  .ctrl{gap:8px}
  #timeLbl{width:92px;font-size:9pt}
  .pgrid{grid-template-columns:1fr;gap:4px}
  .pgrid .span3{grid-column:1}
  .pgrid label,.pgrid label.r,.pgrid label.top{padding:6px 0 0;font-size:9pt}
  .pbtns .btn{flex:1}
  .tlCard{padding:8px}
  .tlbar{flex-wrap:nowrap;overflow-x:auto;scrollbar-width:none;padding-bottom:4px}
  .tlbar::-webkit-scrollbar{display:none}
  .tlbar>*{flex:none}
  .steps{display:flex;overflow-x:auto;gap:16px;scrollbar-width:none;font-size:9pt}
  .steps::-webkit-scrollbar{display:none}
  .steps div{flex:none}
  .prog{position:sticky;bottom:calc(-20px - env(safe-area-inset-bottom));z-index:30;margin:10px -12px 0;border-left:0;border-right:0;
    padding:8px 12px calc(10px + env(safe-area-inset-bottom));box-shadow:0 -10px 24px rgba(0,0,0,.55)}
  #progDetail{font-size:9pt;max-height:2.7em;overflow:hidden}
  .foot .btn{flex:1}
  .foot .btn.accent{flex:2}
  .warn .btn{margin:0 10px 10px;flex:1}
  .mbox{padding:16px 16px;width:94%}
  .mbtns .btn{flex:1}
  .dropTitle{font-size:14pt}
  .dropSub{font-size:9pt}
}
@media(max-width:760px) and (orientation:landscape){
  #page.narrow #videoFrame{height:min(60dvh,50vw)}
}
'''

APP_JS = r'''/* Khmer Dubber Editor - web front end.  Same editor as the desktop version:
   timeline, lines table, edit panel, undo/redo, projects, .srt, preview. */
"use strict";
const $ = (id) => document.getElementById(id);
const RULER_H = 24, ZH_Y = 32, ZH_H = 34, KM_Y = 74, KM_H = 50, TL_H = KM_Y + KM_H + 14;
const C = {panel:"#121215", muted:"#8d887c", accent:"#c9a45c", accentL:"#e6cf9a", accentFg:"#15110a",
  block:"#3a3220", blockEdge:"#6e5a30", muteFill:"#232327", muteEdge:"#3a3a40",
  refFill:"#141418", refEdge:"#25252b", playhead:"#e8d3a0", gold:"#e6cf9a"};
const KM_FONT = '"Leelawadee UI","Noto Sans Khmer","Khmer OS","Khmer UI",sans-serif';
const UI_FONT = '"Segoe UI","Noto Sans","DejaVu Sans",sans-serif';

const S = {
  cfg: null, segments: [], rows: [], total: 0, mediaLen: 0, sel: null, undo: [], redo: [],
  dirty: false, projDirty: false, busy: false, saved: true, hasVideo: false, dubbed: false,
  videoName: "", mode: "original", pps: 40, playhead: 0, drag: null, scrub: false,
  loading: false, ver: 0, resume: false, set: {}, savedOnce: false,
};
const sets = {voice: "Female (Sreymom)", engine: "Microsoft", accuracy: "Balanced",
  pause: true, novoice: false, burn: false, auto_voice: true, remember: false};

/* ------------------------------------------------------------ helpers */
const fmtTime = (s) => { s = Math.max(0, Math.floor(s)); return s >= 3600
  ? `${Math.floor(s/3600)}:${String(Math.floor(s%3600/60)).padStart(2,"0")}:${String(s%60).padStart(2,"0")}`
  : `${String(Math.floor(s/60)).padStart(2,"0")}:${String(s%60).padStart(2,"0")}`; };
const shorten = (t, n = 70) => t.length <= n ? t : t.slice(0, n - 3) + "...";
const clone = (o) => JSON.parse(JSON.stringify(o));
const detail = (t) => { $("progDetail").textContent = t; };

async function api(url, body, opts = {}) {
  const r = await fetch(url, body === undefined ? {} :
    {method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body)});
  if (opts.raw) return r;
  let j = {}; try { j = await r.json(); } catch (e) {}
  if (!r.ok) { const err = new Error(j.error || ("Server error " + r.status)); err.data = j; throw err; }
  return j;
}

/* ------------------------------------------------------------ dialogs */
function dialog(title, text, buttons, input) {
  return new Promise((res) => {
    $("mTitle").textContent = title; $("mBody").textContent = text;
    const inp = $("mInput"); inp.hidden = !input; inp.value = "";
    const bx = $("mBtns"); bx.innerHTML = "";
    const close = (v) => { $("modal").hidden = true; res(v); };
    buttons.forEach((b, i) => {
      const el = document.createElement("button");
      el.className = "btn" + (b.accent ? " accent" : ""); el.textContent = b.label;
      el.onclick = () => close(input ? (b.value ? inp.value : null) : b.value);
      bx.appendChild(el); if (i === buttons.length - 1) setTimeout(() => (input ? inp : el).focus(), 30);
    });
    inp.onkeydown = (e) => { if (e.key === "Enter") close(inp.value); if (e.key === "Escape") close(null); };
    $("modal").hidden = false;
  });
}
const info = (t, x) => dialog(t, x, [{label: "OK", value: true, accent: true}]);
const yesno = (t, x) => dialog(t, x, [{label: "No", value: false}, {label: "Yes", value: true, accent: true}]);
const ask = (t, x) => dialog(t, x, [{label: "Cancel", value: false}, {label: "OK", value: true, accent: true}], true);

/* ------------------------------------------------------------ settings widgets */
function segGroup(id, values, key) {
  const box = $(id); box.innerHTML = "";
  values.forEach((v) => {
    const b = document.createElement("button"); b.className = "segbtn" + (sets[key] === v ? " on" : "");
    b.textContent = v; b.onclick = () => { sets[key] = v; [...box.children].forEach((c) => c.classList.toggle("on", c === b)); };
    box.appendChild(b);
  });
}
function toggle(parent, text, get, set, onChange, left) {
  const row = document.createElement("div"); row.className = "tg" + (left ? " inl" : "") + (get() ? " on" : "");
  row.innerHTML = `<span class="lbl"></span><span class="pill"></span>`; row.firstChild.textContent = text;
  row.onclick = () => { set(!get()); row.classList.toggle("on", get()); onChange && onChange(); };
  row.sync = () => row.classList.toggle("on", get());
  parent.appendChild(row); return row;
}
const toggles = [];
function buildSidebar() {
  segGroup("voiceSeg", S.cfg.voices, "voice"); segGroup("engineSeg", ["Microsoft", "Google"], "engine");
  segGroup("accSeg", S.cfg.accuracy, "accuracy");
  [["Pause to edit after translating", "pause"], ["Remove the original human voice", "novoice"],
   ["Burn Khmer subtitles into video", "burn"], ["Auto male / female voice", "auto_voice"],
   ["Remember my progress", "remember"]].forEach(([t, k]) =>
    toggles.push(toggle($("checks"), t, () => sets[k], (v) => (sets[k] = v))));
  const so = $("soundSl"), sh = $("shiftSl");
  const so_show = () => ($("soundVal").textContent = +so.value === 0 ? "Off" : `${Math.round(so.value)}%`);
  const sh_show = () => { const v = +sh.value; $("shiftVal").textContent = Math.abs(v) < 0.05 ? "on time" : `${Math.abs(v).toFixed(1)} s ${v > 0 ? "later" : "earlier"}`; };
  so.oninput = so_show; sh.oninput = sh_show; so_show(); sh_show();
  const fill = (el) => { const f = () => el.style.background = `linear-gradient(to right,${C.accent} ${(el.value-el.min)/(el.max-el.min)*100}%,#2a2a31 0)`; el.addEventListener("input", f); f(); };
  /* (Firefox draws its own filled track; Chrome keeps the plain track) */

  const mk = (box, items) => items.forEach(([key, label, fn]) => {
    const row = document.createElement("div"); row.className = "item";
    row.innerHTML = `<i></i><button></button>`; row.lastChild.textContent = label; row.lastChild.onclick = () => { if (!row.classList.contains("dis")) fn(); };
    box.appendChild(row); sideBtns[key] = row;
  });
  mk($("fileItems"), [["choose", "Choose video...", chooseVideo], ["openproj", "Open project...", () => loadProject()],
    ["saveproj", "Save project...", saveProject], ["save", "Save video...", saveCopy],
    ["folder", "Open folder", openFolder], ["srt", "Export .srt", exportSrt],
    ["copysrt", "Copy subtitles", copySrt], ["copykm", "Copy Khmer text", copyKhmer]]);
  mk($("editItems"), [["undo", "Undo", doUndo], ["redo", "Redo", doRedo], ["split", "Split at playhead", doSplit],
    ["lines", "Split lines", doSplitLines], ["merge", "Merge next", doMerge], ["delete", "Delete", doDelete],
    ["add", "Add line", doAdd]]);
  $("sbRender").onclick = renderNow;
  const isMob = () => matchMedia("(max-width:760px)").matches;
  const toggleSide = () => $("side").classList.toggle(isMob() ? "open" : "closed");
  $("sideToggle").onclick = toggleSide; $("menuBtn").onclick = toggleSide;
  $("sideVeil").onclick = () => $("side").classList.remove("open");
  $("sideBody").addEventListener("click", (e) => { if (isMob() && e.target.closest(".item button, button.primary")) setTimeout(() => $("side").classList.remove("open"), 60); });
  matchMedia("(max-width:760px)").addEventListener("change", () => $("side").classList.remove("open"));
  document.addEventListener("keydown", (e) => { if (e.key === "Escape") $("side").classList.remove("open"); });
  if (!isMob() && innerWidth < 1100) $("side").classList.add("closed");
}
const sideBtns = {};
function settings() {
  return {voice: sets.voice, sound: +$("soundSl").value, shift: +$("shiftSl").value, engine: sets.engine,
    accuracy: sets.accuracy, novoice: sets.novoice, burn: sets.burn, auto_voice: sets.auto_voice,
    pause: sets.pause, remember: sets.remember};
}
function applySettings(st) {
  for (const k of ["voice", "engine", "accuracy", "novoice", "burn", "auto_voice", "pause"]) if (k in st) sets[k] = st[k];
  if ("sound" in st) $("soundSl").value = st.sound; if ("shift" in st) $("shiftSl").value = st.shift;
  $("soundSl").oninput(); $("shiftSl").oninput();
  segGroup("voiceSeg", S.cfg.voices, "voice"); segGroup("engineSeg", ["Microsoft", "Google"], "engine");
  segGroup("accSeg", S.cfg.accuracy, "accuracy"); toggles.forEach((t) => t.sync());
}

/* ------------------------------------------------------------ steps / buttons */
function setStep(idx, text, pct) {
  [...$("steps").children].forEach((l, i) => {
    if (i < idx) { l.textContent = "✓  " + S.cfg.steps[i]; l.style.color = "#7fd6a4"; }
    else if (i === idx) { l.textContent = "●  " + S.cfg.steps[i]; l.style.color = C.accentL; }
    else { l.textContent = "○  " + S.cfg.steps[i]; l.style.color = C.muted; }
  });
  detail(text); $("barFill").style.width = pct + "%";
}
function updateButtons() {
  const b = S.busy, has = S.segments.length > 0;
  const en = (id, on) => { $(id).disabled = !on; };
  en("chooseBtn", !b); en("cancelBtn", b); en("renderBtn", !b && has);
  $("renderBtn").textContent = S.dubbed ? "Update dubbed video" : "Make dubbed video";
  en("saveBtn", !b && S.dubbed); en("folderBtn", !b && S.dubbed && S.savedOnce);
  ["splitBtn", "sentBtn", "mergeBtn", "delBtn", "addBtn"].forEach((i) => en(i, !b && has));
  en("undoBtn", !b && S.undo.length > 0); en("redoBtn", !b && S.redo.length > 0); en("srtBtn", has);
  const on = {choose: !b, openproj: !b, saveproj: !b && has, save: !b && S.dubbed, folder: !b && S.dubbed && S.savedOnce,
    srt: has, copysrt: has, copykm: has, undo: !b && S.undo.length > 0, redo: !b && S.redo.length > 0,
    split: !b && has, lines: !b && has, merge: !b && has, delete: !b && has, add: !b && has};
  for (const k in on) sideBtns[k].classList.toggle("dis", !on[k]);
  $("sbRender").disabled = b || !has; $("sbRender").textContent = $("renderBtn").textContent;
  setPanelEnabled(!b && S.sel !== null);
}

/* ------------------------------------------------------------ player */
const V = $("video");
V.addEventListener("loadedmetadata", () => $("videoFrame").classList.toggle("tall", V.videoHeight > V.videoWidth));
const curPath = () => (S.mode === "dubbed" && S.dubbed ? "/media/dubbed?v=" + S.ver : "/media/original?v=" + S.ver);
function loadVideo(url, startSec = 0, autoplay = false) {
  V.src = url;
  V.onloadedmetadata = () => { if (startSec) V.currentTime = startSec; S.mediaLen = V.duration || 0; drawTimeline(); };
  V.load(); if (autoplay) V.play().catch(() => {});
  $("playBtn").textContent = autoplay ? "Pause" : "Play";
}
function togglePlay() {
  if (!V.src || !S.hasVideo) return;
  if (V.paused) { V.play().catch(() => {}); $("playBtn").textContent = "Pause"; }
  else { V.pause(); $("playBtn").textContent = "Play"; }
}
V.onended = () => { $("playBtn").textContent = "Play"; };
function setMode(m) {
  if (m === "dubbed" && !S.dubbed) { info("Not ready", "The Khmer version is not ready yet."); return; }
  S.mode = m; $("modeDub").classList.toggle("on", m === "dubbed"); $("modeOrig").classList.toggle("on", m === "original");
}
function switchSource(m) {
  if (m === "dubbed" && !S.dubbed) { info("Not ready", "The Khmer version is not ready yet."); return; }
  setMode(m); if (!S.hasVideo) return;
  const pos = V.currentTime || 0, playing = !V.paused;
  loadVideo(curPath(), pos, playing);
}
function seekTo(t) {
  S.playhead = Math.max(t, 0);
  if (S.hasVideo && V.src) { try { V.currentTime = S.playhead; } catch (e) {} }
  drawPlayhead();
}
function tick() {
  document.querySelectorAll('input[type=range]').forEach((el) => el.style.setProperty('--p', ((el.value - el.min) / (el.max - el.min) * 100) + '%'));
  if (S.hasVideo && V.src && V.duration > 0) {
    const cur = V.currentTime, len = V.duration;
    S.mediaLen = len;
    if (!seekDrag) $("seek").value = cur / len * 1000;
    $("timeLbl").textContent = `${fmtTime(cur)} / ${fmtTime(len)}`;
    if (!S.scrub && !S.drag) {
      S.playhead = cur;
      if (Math.abs(totalLen() - S.tlLen) > 0.5) drawTimeline(); else drawPlayhead(!V.paused);
    }
    caption(cur);
  }
}
function caption(t) {
  for (const s of S.segments) if (s.start <= t && t <= s.end) { $("caption").textContent = s.km !== "..." ? s.km : ""; return; }
  $("caption").textContent = "";
}
let seekDrag = false;
const seekRelease = () => { if (!seekDrag) return; seekDrag = false; if (V.duration > 0) V.currentTime = $("seek").value / 1000 * V.duration; };
$("seek").addEventListener("pointerdown", () => { seekDrag = true; window.addEventListener("pointerup", seekRelease, {once: true}); });
$("seek").addEventListener("keyup", () => { seekDrag = true; seekRelease(); });

/* ------------------------------------------------------------ timeline */
const tl = $("tl"), ctx2 = tl.getContext("2d");
const totalLen = () => Math.max(S.total, S.mediaLen, Math.max(0, ...S.segments.map((s) => s.end)) + 1, 10);
const t2x = (t) => t * S.pps, x2t = (x) => Math.max(x / S.pps, 0);
function rrect(c, x0, y0, x1, y1, r, fill, edge, lw) {
  r = Math.max(Math.min(r, (x1 - x0) / 2, (y1 - y0) / 2), 0.5);
  c.beginPath(); c.moveTo(x0 + r, y0); c.arcTo(x1, y0, x1, y1, r); c.arcTo(x1, y1, x0, y1, r);
  c.arcTo(x0, y1, x0, y0, r); c.arcTo(x0, y0, x1, y0, r); c.closePath();
  c.fillStyle = fill; c.fill(); if (edge) { c.strokeStyle = edge; c.lineWidth = lw || 1; c.stroke(); }
}
function drawTimeline() {
  const wrap = $("tlWrap"), total = totalLen(); S.tlLen = total;
  const width = Math.max(Math.floor(total * S.pps) + 200, wrap.clientWidth);
  if (tl.width !== width) tl.width = width; tl.height = TL_H;
  const c = ctx2; c.clearRect(0, 0, width, TL_H);
  c.fillStyle = "#050506"; c.fillRect(0, 0, width, TL_H);
  c.fillStyle = C.panel; c.fillRect(0, 0, width, RULER_H);
  c.fillStyle = "#08080a"; c.fillRect(0, ZH_Y - 4, width, ZH_H + 8);
  c.fillStyle = "#0a0a0d"; c.fillRect(0, KM_Y - 4, width, KM_H + 8);
  const step = [0.5, 1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 1800].find((s) => s * S.pps >= 70) || 3600;
  c.font = `9px ${UI_FONT}`; c.textBaseline = "middle";
  c.strokeStyle = "#26262c"; c.lineWidth = 1; c.beginPath(); c.moveTo(0, RULER_H - .5); c.lineTo(width, RULER_H - .5); c.stroke();
  for (let k = 0; k * step <= total + step; k++) {
    const x = k * step * S.pps; c.strokeStyle = C.muted; c.lineWidth = 1;
    c.beginPath(); c.moveTo(Math.round(x) + .5, 5); c.lineTo(Math.round(x) + .5, RULER_H); c.stroke();
    c.fillStyle = C.muted; c.fillText(fmtTime(k * step), x + 5, RULER_H / 2);
  }
  for (const sg of S.segments) {
    const x0 = t2x(sg.os ?? sg.start), x1 = t2x(sg.oe ?? sg.end);
    rrect(c, x0, ZH_Y, x1, ZH_Y + ZH_H, 5, C.refFill, C.refEdge);
    const n = Math.floor((x1 - x0 - 8) / 9);
    if (n > 0) { c.fillStyle = C.muted; c.font = `9px ${UI_FONT}`; c.textBaseline = "middle"; c.fillText(sg.zh.slice(0, n), x0 + 6, ZH_Y + ZH_H / 2); }
  }
  if (!S.segments.length) { c.fillStyle = C.muted; c.font = `10px ${UI_FONT}`;
    c.fillText("The timeline appears here after the video has been translated.", 14, KM_Y + 14); }
  S.segments.forEach((sg, i) => {
    const x0 = t2x(sg.start), x1 = t2x(sg.end), sel = i === S.sel;
    let fill, edge;
    if (sg.mute) [fill, edge] = [C.muteFill, C.muteEdge]; else [fill, edge] = sel ? [C.accent, C.accentL] : [C.block, C.blockEdge];
    rrect(c, x0, KM_Y, x1, KM_Y + KM_H, 8, fill, edge, sel ? 2 : 1);
    const n = Math.floor((x1 - x0 - 14) / 7);
    if (n > 0) { c.fillStyle = sel ? C.accentFg : C.accentL; c.font = `10px ${KM_FONT}`; c.textBaseline = "middle";
      c.fillText((sg.km || "").replace(/\n/g, " ").slice(0, n), x0 + 9, KM_Y + KM_H / 2); }
    if (sg.locked && x1 - x0 > 30) { c.fillStyle = C.gold; c.font = `8px ${UI_FONT}`; c.textAlign = "right"; c.textBaseline = "alphabetic";
      c.fillText("fit", x1 - 8, KM_Y + KM_H - 6); c.textAlign = "left"; }
    if (sel) { c.strokeStyle = C.accentFg; c.lineWidth = 2; c.lineCap = "round";
      for (const x of [x0 + 5, x1 - 5]) { c.beginPath(); c.moveTo(x, KM_Y + 14); c.lineTo(x, KM_Y + KM_H - 14); c.stroke(); } c.lineCap = "butt"; }
  });
  S.tlImg = null; drawPlayhead();
}
function drawPlayhead(follow) {
  /* playhead is a DOM line so the canvas does not need a full redraw 10x a second */
  let ph = $("ph"); const wrap = $("tlWrap");
  if (!ph) { ph = document.createElement("canvas"); ph.id = "ph"; ph.style.cssText = "position:absolute;top:0;left:0;pointer-events:none"; wrap.style.position = "relative"; wrap.appendChild(ph); }
  const x = t2x(S.playhead);
  ph.width = 76; ph.height = TL_H; ph.style.left = (Math.round(x) - 8) + "px";
  const c = ph.getContext("2d"); c.clearRect(0, 0, 76, TL_H);
  c.fillStyle = C.playhead; c.fillRect(8, 0, 1, TL_H);
  c.beginPath(); c.moveTo(2, 0); c.lineTo(14, 0); c.lineTo(8, 9); c.closePath(); c.fill();
  const label = fmtTime(S.playhead); c.font = `bold 9px ${UI_FONT}`; const tw = c.measureText(label).width;
  rrect(c, 16, 3, 16 + tw + 10, 19, 3, C.playhead); c.fillStyle = C.accentFg; c.textBaseline = "middle"; c.fillText(label, 21, 11.5);
  if (follow && (x > wrap.scrollLeft + wrap.clientWidth - 40 || x < wrap.scrollLeft)) wrap.scrollLeft = Math.max(x - 60, 0);
}
function setZoom(v) { S.pps = Math.min(Math.max(v, 5), 200); $("zoomSl").value = S.pps; drawTimeline(); }
function fitZoom() { const w = Math.max($("tlWrap").clientWidth, 400); setZoom((w - 60) / Math.max(totalLen(), 1)); $("tlWrap").scrollLeft = 0; }
$("zoomSl").oninput = () => setZoom(+$("zoomSl").value);
$("fitBtn").onclick = fitZoom;
new ResizeObserver(() => drawTimeline()).observe($("tlWrap"));
new ResizeObserver((en) => { const w = en[0].contentRect.width; $("page").classList.toggle("narrow", w < 620); }).observe($("page"));

const COARSE = matchMedia("(pointer:coarse)").matches;
function hit(x, y) {
  const pad = COARSE ? 10 : 4, hx = COARSE ? 10 : 3;
  if (!(y >= KM_Y - pad && y <= KM_Y + KM_H + pad)) return null;
  for (let i = S.segments.length - 1; i >= 0; i--) {
    const sg = S.segments[i], x0 = t2x(sg.start), x1 = t2x(sg.end);
    if (x >= x0 - hx && x <= x1 + hx) { const z = Math.min(COARSE ? 20 : 8, (x1 - x0) / 3);
      return [i, x - x0 <= z ? "l" : (x1 - x <= z ? "r" : "m")]; }
  }
  return null;
}
const evXY = (e) => { const r = tl.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
function snap(t, pts) { const th = 8 / S.pps; let best = t, gap = th; for (const p of pts) if (Math.abs(p - t) < gap) { best = p; gap = Math.abs(p - t); } return best; }
tl.addEventListener("mousemove", (e) => {
  if (S.drag || S.scrub) return;
  const [x, y] = evXY(e); const h = S.busy ? null : hit(x, y);
  tl.style.cursor = h ? (h[1] === "m" ? "move" : "ew-resize") : "default";
});
tl.addEventListener("pointerdown", (e) => {
  if (e.pointerType === "mouse" && e.button !== 0) return;
  S.resume = false; if (S.hasVideo && !V.paused) { V.pause(); } $("playBtn").textContent = "Play";
  applyPanel();
  const [x, y] = evXY(e), wrap = $("tlWrap");
  const h = (S.busy || y < RULER_H) ? null : hit(x, y);
  let pan = null;
  if (h) {
    const [i, mode] = h; select(i); const sg = S.segments[i];
    const pts = [0, S.playhead]; S.segments.forEach((o) => { if (o !== sg) pts.push(o.start, o.end); });
    S.drag = {seg: sg, mode, x0: x, s0: sg.start, e0: sg.end, moved: false, pts};
  } else if (e.pointerType === "touch" && y < RULER_H) {
    pan = {sx: e.clientX, sl: wrap.scrollLeft};              /* finger on the ruler = slide the timeline */
  } else {
    if (y >= RULER_H && !S.busy) select(null);
    S.scrub = true; seekTo(x2t(x));
  }
  const edge = (mx) => { const vx = mx - wrap.scrollLeft, m = 36;
    if (vx > wrap.clientWidth - m) wrap.scrollLeft += 14; else if (vx < m && wrap.scrollLeft > 0) wrap.scrollLeft -= 14; };
  const move = (ev) => {
    if (ev.pointerId !== e.pointerId) return;
    if (pan) { wrap.scrollLeft = pan.sl - (ev.clientX - pan.sx); return; }
    const [mx] = evXY(ev);
    if (S.scrub) { edge(mx); seekTo(x2t(mx)); return; }
    const d = S.drag; if (!d) return;
    const dt = (mx - d.x0) / S.pps;
    if (!d.moved && Math.abs(mx - d.x0) < (COARSE ? 6 : 3)) return;
    if (!d.moved) { d.moved = true; S.undo.push([clone(S.segments), S.sel]); S.redo.length = 0; }
    edge(mx);
    const sg = d.seg;
    if (d.mode === "m") {
      let ns = Math.max(d.s0 + dt, 0), ne = ns + (d.e0 - d.s0);
      const a1 = snap(ns, d.pts) - ns, a2 = snap(ne, d.pts) - ne;
      const adj = (a1 !== 0 && (a2 === 0 || Math.abs(a1) <= Math.abs(a2))) ? a1 : a2;
      ns = Math.max(ns + adj, 0); sg.start = ns; sg.end = ns + (d.e0 - d.s0);
    } else if (d.mode === "l") {
      sg.start = Math.min(Math.max(snap(d.s0 + dt, d.pts), 0), d.e0 - 0.2); sg.locked = true;
    } else { sg.end = Math.max(snap(d.e0 + dt, d.pts), d.s0 + 0.2); sg.locked = true; }
    setTimeFields(sg); drawTimeline();
  };
  const up = (ev) => {
    if (ev && ev.pointerId !== e.pointerId) return;
    window.removeEventListener("pointermove", move); window.removeEventListener("pointerup", up); window.removeEventListener("pointercancel", up);
    const d = S.drag; S.drag = null; S.scrub = false; pan = null;
    if (d && d.moved) { const sg = d.seg; S.segments.sort((a, b) => a.start - b.start);
      S.sel = S.segments.indexOf(sg); afterEdit(); loadPanel(); }
  };
  window.addEventListener("pointermove", move); window.addEventListener("pointerup", up); window.addEventListener("pointercancel", up);
  e.preventDefault();
});
$("tlWrap").addEventListener("wheel", (e) => {
  if (e.ctrlKey) { e.preventDefault(); setZoom(S.pps * (e.deltaY < 0 ? 1.2 : 1 / 1.2)); }
  else if (!e.shiftKey && Math.abs(e.deltaY) > Math.abs(e.deltaX)) { e.preventDefault(); $("tlWrap").scrollLeft += e.deltaY; }
}, {passive: false});

/* ------------------------------------------------------------ lines table */
function refreshTree() {
  const rows = S.segments.length ? S.segments : S.rows, tb = $("tree").tBodies[0];
  tb.innerHTML = "";
  rows.forEach((sg, i) => {
    const tr = document.createElement("tr"); tr.className = (i % 2 ? "odd" : "even") + (i === S.sel ? " sel" : "");
    tr.dataset.i = i;
    for (const t of [fmtTime(sg.start), sg.zh, sg.km]) { const td = document.createElement("td"); td.textContent = t; tr.appendChild(td); }
    tb.appendChild(tr);
  });
  const s = tb.querySelector("tr.sel"); if (s) s.scrollIntoView({block: "nearest"});
}
$("tree").tBodies[0].addEventListener("click", (e) => {
  const tr = e.target.closest("tr"); if (!tr || S.busy) return;
  const i = +tr.dataset.i; if (i !== S.sel && i < S.segments.length) { applyPanel(); select(i); }
  if (COARSE && i < S.segments.length && S.hasVideo) seekTo(S.segments[i].start);
});
$("tree").tBodies[0].addEventListener("dblclick", (e) => {
  const tr = e.target.closest("tr"); if (tr && S.segments.length) seekTo(S.segments[+tr.dataset.i].start);
});
function select(i) { S.sel = i; refreshTree(); loadPanel(); drawTimeline(); updateButtons(); }

/* ------------------------------------------------------------ edit panel */
function setPanelEnabled(on) {
  for (const id of ["tZh", "tKm", "fStart", "fEnd", "cbVoice", "cbSpeed", "fVol", "retrBtn", "hearBtn"]) $(id).disabled = !on;
}
function setTimeFields(sg) { $("fStart").value = sg.start.toFixed(2); $("fEnd").value = sg.end.toFixed(2); }
let mute, lock;
function buildPanel() {
  const vs = $("cbVoice"); ["Default", ...S.cfg.voices].forEach((v) => vs.add(new Option(v, v)));
  S.cfg.speeds.forEach((v) => $("cbSpeed").add(new Option(v, v)));
  const st = {mute: false, lock: false};
  mute = toggle($("panelToggles"), "Mute this voice", () => st.mute, (v) => (st.mute = v), applyPanel, true);
  lock = toggle($("panelToggles"), "Fit exactly in block", () => st.lock, (v) => (st.lock = v), applyPanel, true);
  mute.st = lock.st = st;
  for (const id of ["tZh", "tKm", "fStart", "fEnd"]) $(id).addEventListener("blur", () => applyPanel());
  $("fStart").onchange = $("fEnd").onchange = () => applyPanel();
  $("cbVoice").onchange = $("cbSpeed").onchange = () => applyPanel();
  $("fVol").oninput = () => ($("volLbl").textContent = Math.round($("fVol").value) + "%");
  $("fVol").onchange = () => applyPanel();
  $("retrBtn").onclick = retranslate; $("hearBtn").onclick = previewVoice;
}
function loadPanel() {
  S.loading = true;
  try {
    const on = S.sel !== null && S.sel < S.segments.length && !S.busy;
    $("tZh").value = ""; $("tKm").value = "";
    if (!on) { $("panelTitle").textContent = "EDIT LINE  -  select a block on the timeline"; $("fStart").value = ""; $("fEnd").value = ""; setPanelEnabled(false); return; }
    const sg = S.segments[S.sel];
    setPanelEnabled(true);
    $("panelTitle").textContent = `EDIT LINE  ${S.sel + 1} of ${S.segments.length}`;
    $("tZh").value = sg.zh; $("tKm").value = sg.km === "..." ? "" : sg.km; setTimeFields(sg);
    $("cbVoice").value = sg.voice || "Default";
    const spd = +(sg.speed || 0); $("cbSpeed").value = spd <= 0 ? "Auto" : `${+spd.toFixed(2)}x`;
    const vol = Math.round(+(sg.vol ?? 1) * 100); $("fVol").value = vol; $("volLbl").textContent = vol + "%";
    mute.st.mute = !!sg.mute; lock.st.lock = !!sg.locked; mute.sync(); lock.sync();
  } finally { S.loading = false; }
}
async function applyPanel() {
  if (S.loading || S.busy || S.sel === null || S.sel >= S.segments.length) return;
  const sg = S.segments[S.sel];
  let st = Math.round(parseFloat($("fStart").value) * 100) / 100, en = Math.round(parseFloat($("fEnd").value) * 100) / 100;
  if (isNaN(st) || isNaN(en)) { st = Math.round(sg.start * 100) / 100; en = Math.round(sg.end * 100) / 100; }
  if (st < 0 || en - st < 0.1) { st = Math.round(sg.start * 100) / 100; en = Math.round(sg.end * 100) / 100; setTimeFields(sg); }
  const spd = $("cbSpeed").value; let speed = spd === "Auto" ? 0 : parseFloat(spd);
  if (isNaN(speed)) speed = 0;
  const voice = $("cbVoice").value;
  const nw = {zh: $("tZh").value.trim(), km: $("tKm").value.trim(), start: st, end: en, voice: voice === "Default" ? null : voice,
    speed, vol: Math.round($("fVol").value) / 100, mute: mute.st.mute, locked: lock.st.lock};
  const od = {zh: sg.zh, km: sg.km === "..." ? "" : sg.km, start: Math.round(sg.start * 100) / 100, end: Math.round(sg.end * 100) / 100,
    voice: sg.voice || null, speed: +(sg.speed || 0), vol: Math.round(+(sg.vol ?? 1) * 100) / 100, mute: !!sg.mute, locked: !!sg.locked};
  if (JSON.stringify(nw) === JSON.stringify(od)) return;
  pushUndo(); Object.assign(sg, nw);
  if (nw.start !== od.start) { S.segments.sort((a, b) => a.start - b.start); S.sel = S.segments.indexOf(sg); }
  afterEdit();
  if (/[\n。！？!?…；;.។៕]/.test(sg.zh + sg.km)) {       /* text typed on 2-3 lines -> 2-3 boxes */
    try {
      const r = await api("/api/split_lines", {segs: [sg]});
      if (r.segs.length > 1) { const i = S.segments.indexOf(sg); if (i >= 0) { S.segments.splice(i, 1, ...r.segs); S.sel = i; afterEdit(); loadPanel(); translatePending(r.segs); } }
    } catch (e) {}
  }
}

/* ------------------------------------------------------------ editing */
function pushUndo() { S.undo.push([clone(S.segments), S.sel]); if (S.undo.length > 100) S.undo.shift(); S.redo.length = 0; }
function restore(snap) { S.segments = snap[0]; S.sel = snap[1]; if (S.sel !== null && S.sel >= S.segments.length) S.sel = null; afterEdit(); loadPanel(); }
function doUndo() { if (S.busy || !S.undo.length) return; applyPanel(); S.redo.push([clone(S.segments), S.sel]); restore(S.undo.pop()); }
function doRedo() { if (S.busy || !S.redo.length) return; S.undo.push([clone(S.segments), S.sel]); restore(S.redo.pop()); }
function afterEdit() {
  S.dirty = true; S.projDirty = true;
  if (S.dubbed && !S.busy) detail("You changed something. Press 'Update dubbed video' to apply it.");
  refreshTree(); drawTimeline(); updateButtons();
}
function doSplit() {
  if (S.busy || !S.segments.length) return; applyPanel();
  const t = S.playhead; let idx = null;
  const inside = (s) => s.start + 0.1 < t && t < s.end - 0.1;
  if (S.sel !== null && inside(S.segments[S.sel])) idx = S.sel; else idx = S.segments.findIndex(inside);
  if (idx === null || idx < 0) { detail("Move the gold playhead inside a block, then press Split."); return; }
  pushUndo(); const sg = S.segments[idx], frac = (t - sg.start) / (sg.end - sg.start), zh = sg.zh;
  const k = zh.length > 1 ? Math.min(Math.max(Math.round(zh.length * frac), 1), Math.max(zh.length - 1, 1)) : zh.length;
  const words = (sg.km === "..." ? "" : sg.km).split(" "); let km1, km2;
  if (words.length > 1) { const kk = Math.min(Math.max(Math.round(words.length * frac), 1), words.length - 1); km1 = words.slice(0, kk).join(" "); km2 = words.slice(kk).join(" "); }
  else { km1 = words.join(" "); km2 = ""; }
  const b = clone(sg); Object.assign(b, {start: t, zh: zh.slice(k), km: km2});
  const os = sg.os ?? sg.start, oe = sg.oe ?? sg.end;
  if (os < t && t < oe) { sg.oe = t; b.os = t; }
  Object.assign(sg, {end: t, zh: zh.slice(0, k), km: km1});
  S.segments.splice(idx + 1, 0, b); S.sel = idx + 1; afterEdit(); loadPanel();
}
async function doSplitLines() {
  if (S.busy || !S.segments.length) return; await applyPanel();
  const r = await api("/api/split_lines", {segs: S.segments}); const nw = r.segs;
  if (nw.length === S.segments.length) { detail("No box has more than one line of text."); return; }
  pushUndo(); const added = nw.length - S.segments.length; S.segments = nw; S.sel = null; afterEdit(); loadPanel();
  detail(`Cut into ${added} more box(es).`); translatePending(nw, added);
}
function translatePending(list, added) {
  const pend = list.filter((x) => (x.km === "..." || x.km === "") && x.zh.trim());
  if (!pend.length) return;
  if (added) detail(`Cut into ${added} more box(es). Translating the new pieces...`);
  (async () => { for (const sg of pend) { try {
      const r = await api("/api/translate", {text: sg.zh, engine: sets.engine});
      if (S.segments.includes(sg)) { pushUndo(); sg.km = r.km; afterEdit(); loadPanel(); } } catch (e) {} } })();
}
async function doMerge() {
  if (S.busy || S.sel === null || S.sel + 1 >= S.segments.length) { detail("Select a block that has another block after it, then Merge."); return; }
  await applyPanel(); pushUndo();
  const a = S.segments[S.sel], b = S.segments[S.sel + 1];
  a.zh += b.zh; const ka = a.km === "..." ? "" : a.km, kb = b.km === "..." ? "" : b.km;
  a.km = (ka + " " + kb).trim(); a.end = Math.max(a.end, b.end); a.oe = Math.max(a.oe ?? a.end, b.oe ?? b.end);
  S.segments.splice(S.sel + 1, 1); afterEdit(); loadPanel();
}
function doDelete() { if (S.busy || S.sel === null || S.sel >= S.segments.length) return; pushUndo(); S.segments.splice(S.sel, 1); S.sel = null; afterEdit(); loadPanel(); }
function doAdd() {
  if (S.busy || !S.hasVideo) return; applyPanel(); pushUndo();
  const t = Math.round(S.playhead * 100) / 100, sg = {start: t, end: t + 2, zh: "", km: "", os: t, oe: t + 2};
  S.segments.push(sg); S.segments.sort((a, b) => a.start - b.start); S.sel = S.segments.indexOf(sg);
  afterEdit(); loadPanel(); $("tKm").focus();
}
async function retranslate() {
  if (S.busy || S.sel === null) return; await applyPanel();
  const sg = S.segments[S.sel];
  if (!sg.zh.trim()) { info("Nothing to translate", "Type the Chinese text first."); return; }
  detail("Translating this line...");
  try {
    const r = await api("/api/translate", {text: sg.zh, engine: sets.engine});
    if (!S.segments.includes(sg)) return;
    pushUndo(); sg.km = r.km;
    const p = await api("/api/split_lines", {segs: [sg]});
    if (p.segs.length > 1) { const i = S.segments.indexOf(sg); S.segments.splice(i, 1, ...p.segs); S.sel = i; translatePending(p.segs); }
    afterEdit(); loadPanel(); detail("Line translated again.");
  } catch (e) { info("Something went wrong", e.message); detail("Failed."); }
}
async function previewVoice() {
  if (S.busy || S.sel === null) return; await applyPanel();
  const sg = S.segments[S.sel], text = sg.km.trim(); if (!text || text === "...") return;
  detail("Making a preview of this line...");
  try {
    const r = await api("/api/preview", {text, voice: sg.voice || "", default_voice: sets.voice}, {raw: true});
    if (!r.ok) { const j = await r.json(); throw new Error(j.error); }
    const url = URL.createObjectURL(await r.blob()); const a = $("pvAudio");
    if (S.hasVideo && !V.paused) { V.pause(); $("playBtn").textContent = "Play"; }
    a.src = url; a.play(); detail("Playing this line.");
  } catch (e) { info("Something went wrong", e.message); }
}

/* ------------------------------------------------------------ copy / srt */
async function clip(text, note) {
  try { await navigator.clipboard.writeText(text); } catch (e) {
    const t = document.createElement("textarea"); t.value = text; document.body.appendChild(t); t.select(); document.execCommand("copy"); t.remove(); }
  detail(note);
}
const kmLines = () => S.segments.filter((s) => (s.km || "").trim() && s.km.trim() !== "...").map((s) => s.km.trim());
async function srtText() { return (await api("/api/srt", {segs: S.segments})).text; }
async function copySrt() { await applyPanel(); if (!kmLines().length) return info("No subtitles", "There is no Khmer text yet.");
  clip(await srtText(), "Copied the subtitles (.srt text). Paste them anywhere with Ctrl+V."); }
async function copyKhmer() { await applyPanel(); const l = kmLines(); if (!l.length) return info("No subtitles", "There is no Khmer text yet.");
  clip(l.join("\n"), `Copied ${l.length} Khmer lines. Paste them anywhere with Ctrl+V.`); }
function download(blob, name) { const a = document.createElement("a"); a.href = URL.createObjectURL(blob); a.download = name; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000); }
const baseName = () => (S.videoName || "video").replace(/\.[^.]+$/, "");
async function exportSrt() {
  if (!S.segments.some((s) => (s.km || "").trim())) return info("No subtitles", "There is no Khmer text yet.");
  await applyPanel(); const text = await srtText();
  download(new Blob(["﻿" + text], {type: "application/x-subrip;charset=utf-8"}), baseName() + "_khmer.srt");
  detail("Saved the .srt file (check your Downloads folder).");
  info("Saved", "Saved:\n" + baseName() + "_khmer.srt\n\nIt is in your browser's Downloads folder.");
}
const ctx = $("ctx");
let ctxAt = 0;
function openCtx(tr, cx, cy) {
  if (!tr || !S.segments.length) return; ctxAt = Date.now();
  const i = +tr.dataset.i; if (i !== S.sel) { applyPanel(); select(i); }
  const sg = S.segments[i], km = sg.km === "..." ? "" : sg.km;
  const items = [["Copy Khmer", () => clip(km, "Copied.")], ["Copy Chinese", () => clip(sg.zh, "Copied.")],
    ["Copy both", () => clip(sg.zh + "\n" + km, "Copied.")], null,
    ["Copy ALL Khmer lines", copyKhmer], ["Copy subtitles (.srt text)", copySrt]];
  ctx.innerHTML = ""; items.forEach((it) => { if (!it) return ctx.appendChild(document.createElement("hr"));
    const d = document.createElement("div"); d.textContent = it[0]; d.onclick = () => { ctx.hidden = true; it[1](); }; ctx.appendChild(d); });
  ctx.hidden = false;
  const r = ctx.getBoundingClientRect();
  ctx.style.left = Math.max(6, Math.min(cx, innerWidth - r.width - 6)) + "px";
  ctx.style.top = Math.max(6, Math.min(cy, innerHeight - r.height - 6)) + "px";
}
$("tree").addEventListener("contextmenu", (e) => {
  const tr = e.target.closest("tbody tr"); if (!tr || !S.segments.length) return; e.preventDefault(); openCtx(tr, e.clientX, e.clientY);
});
let lpTimer = 0;
const lpStop = () => { clearTimeout(lpTimer); lpTimer = 0; };
$("tree").addEventListener("touchstart", (e) => {
  const tr = e.target.closest("tbody tr"); if (!tr || e.touches.length !== 1) return;
  const t = e.touches[0]; lpStop(); lpTimer = setTimeout(() => { lpTimer = 0; openCtx(tr, t.clientX, t.clientY); }, 550);
}, {passive: true});
for (const ev of ["touchmove", "touchend", "touchcancel"]) $("tree").addEventListener(ev, lpStop, {passive: true});
document.addEventListener("click", () => { if (Date.now() - ctxAt > 450) ctx.hidden = true; });

/* ------------------------------------------------------------ projects */
async function saveProject() {
  if (S.busy || !S.segments.length || !S.hasVideo) return; await applyPanel();
  let withVideo = false;
  if (S.dubbed) withVideo = await yesno("Save the dubbed video too?",
    "Also keep the finished dubbed video inside the project?\n\nYes = save everything (bigger file)\nNo = save the lines and Khmer voices only");
  detail("Saving the project...");
  const fd = new FormData(); fd.append("data", JSON.stringify({segs: S.segments, total: S.total, settings: settings(), with_video: withVideo}));
  const r = await fetch("/api/project/save", {method: "POST", body: fd});
  if (!r.ok) { info("Could not save", (await r.json()).error); return; }
  download(await r.blob(), baseName() + ".khdub"); S.projDirty = false;
  detail("Project saved (check your Downloads folder).");
  info("Project saved", "It keeps your lines, settings and the Khmer voices" + (withVideo ? " and the dubbed video." : ".") +
    "\n\nNext time press 'Open project...' (or drag the .khdub file onto the window) to keep editing.");
}
async function loadProject(file) {
  if (S.busy || !(await confirmLeave())) return;
  if (!file) { $("fileProj").onchange = () => { const f = $("fileProj").files[0]; $("fileProj").value = ""; if (f) loadProject(f); }; $("fileProj").click(); return; }
  const fd = new FormData(); fd.append("project", file);
  let d; try { const r = await fetch("/api/project/load", {method: "POST", body: fd}); d = await r.json(); if (!r.ok) throw new Error(d.error); }
  catch (e) { info("Could not open", e.message); return; }
  if (!d.video_found) {
    await info("Find the video", "The original video was not found on this computer/server:\n" + d.name + "\n\nPlease choose it again.");
    const f = await pickFile($("fileProjVideo")); if (!f) return;
    const f2 = new FormData(); f2.append("video", f); await fetch("/api/project/video", {method: "POST", body: f2}); d.name = f.name;
  }
  applySettings(d.settings || {});
  Object.assign(S, {segments: d.segs, total: d.total, sel: null, dirty: false, playhead: 0, saved: true, savedOnce: false, hasVideo: true,
    dubbed: !!d.has_dubbed, videoName: d.name, rows: [], ver: S.ver + 1});
  S.undo = []; S.redo = []; $("fileLbl").textContent = shorten(d.name); $("caption").textContent = "";
  setMode(S.dubbed ? "dubbed" : "original"); $("drop").hidden = true; loadVideo(curPath(), 0, false);
  refreshTree(); loadPanel(); updateButtons(); fitZoom(); S.projDirty = false;
  if (S.dubbed) setStep(4, "Project opened with its dubbed video. Press 'Save video...' to keep it, or edit and press 'Update dubbed video'.", 100);
  else setStep(2, "Project opened. Edit the lines, then press 'Make dubbed video'. The saved Khmer voices are reused.", 60);
}
function pickFile(input) { return new Promise((res) => { input.onchange = () => { const f = input.files[0]; input.value = ""; res(f || null); }; input.click(); }); }

/* ------------------------------------------------------------ actions */
async function confirmLeave() {
  if (S.segments.length && S.dirty && S.projDirty)
    return yesno("Unsaved edits", "You have edits that are not saved.\nIf you continue, they will be lost.\n\nTip: 'Save project...' keeps them so you can edit again later.\n\nContinue anyway?");
  if (S.dubbed && !S.saved)
    return yesno("Not saved yet", "You have not saved the dubbed video.\nIf you continue, it will be deleted.\n\nContinue without saving?");
  return true;
}
function chooseVideo() { if (S.busy) return; $("fileVideo").onchange = () => { const f = $("fileVideo").files[0]; $("fileVideo").value = ""; if (f) begin(f); }; $("fileVideo").click(); }

async function begin(file) {
  if (S.busy || !(await confirmLeave())) return;
  let range, res;
  for (;;) {
    range = await ask("Which part do you need?", "Type the part of the video to keep, as start-end.\n\nExample:  10:00-20:00   (minutes:seconds)\nExample:  1:00:00-1:30:00   (hours:minutes:seconds)\n\nLeave it EMPTY to use the whole video. Everything else is removed.");
    if (range === null) return;
    S.busy = true; updateButtons();
    setStep(0, "Uploading your video... 0%", 0);
    try { res = await upload(file, range); break; }
    catch (e) {
      S.busy = false; updateButtons();
      if (e.message.startsWith("Please type it like")) { await info("I did not understand", e.message); continue; }
      setStep(-1, "Failed.", 0); info("One more thing", e.message); return;
    }
  }
  Object.assign(S, {videoName: file.name, dubbed: false, segments: [], rows: [], sel: null, dirty: false, projDirty: false, total: 0,
    playhead: 0, saved: true, savedOnce: false, hasVideo: true, mediaLen: 0, ver: S.ver + 1});
  S.undo = []; S.redo = []; refreshTree(); loadPanel(); drawTimeline(); $("caption").textContent = "";
  $("fileLbl").textContent = shorten(file.name); setMode("original"); $("drop").hidden = true;
  if (!res.trimmed) loadVideo(curPath(), 0, false);
  setStep(0, "Starting...", 0); startPolling();
}
function upload(file, range) {
  return new Promise((ok, bad) => {
    const fd = new FormData(); fd.append("video", file); fd.append("range", range); fd.append("settings", JSON.stringify(settings()));
    const x = new XMLHttpRequest(); x.open("POST", "/api/begin");
    x.upload.onprogress = (e) => e.lengthComputable && setStep(0, `Uploading your video... ${Math.round(e.loaded / e.total * 100)}%`, 0);
    x.onload = () => { let j = {}; try { j = JSON.parse(x.responseText); } catch (e) {} x.status === 200 ? ok(j) : bad(new Error(j.error || "Upload failed")); };
    x.onerror = () => bad(new Error("Could not reach the server.")); x.send(fd);
  });
}
async function renderNow() {
  if (S.busy || !S.segments.length) return; await applyPanel();
  if (!S.segments.some((s) => (s.km || "").trim() && s.km !== "..." && !s.mute)) return info("Nothing to voice", "There is no Khmer text to turn into a voice.");
  let demucs = false;
  if (sets.novoice && !(await api("/api/has_demucs")).has)
    demucs = await yesno("Better voice removal", "To really remove the speaker's voice, the app can install 'demucs' (an AI tool, about 2 GB download, done only once).\n\nYes = install it and use it (best quality)\nNo = basic method (the original sound is muted while people speak; works on every video)\n\nInstall demucs now?");
  try {
    const r = await api("/api/render", {segs: S.segments, settings: settings(), install_demucs: demucs, total: totalLen()});
    if (r.changed) { pushUndo(); S.segments = r.segs; S.sel = null; afterEdit(); loadPanel(); }
  } catch (e) { if (e.data && e.data.segs) {} return info(e.data?.title || "Almost ready", e.message); }
  S.busy = true; updateButtons(); setStep(2, "Starting...", 60); startPolling();
}
async function cancel() { $("cancelBtn").disabled = true; await api("/api/cancel", {}); detail("Cancelling..."); }
function saveCopy() {
  if (!S.dubbed) return; location.href = "/api/download?name=" + encodeURIComponent(S.videoName || "video");
  S.saved = true; S.savedOnce = true; updateButtons(); detail("Saved the video (check your Downloads folder).");
  info("Saved", "Saved:\n" + baseName() + "_khmer.mp4\n\nIt is in your browser's Downloads folder.");
}
async function openFolder() { if (S.savedOnce) { try { await api("/api/open_folder", {}); } catch (e) {} } }

/* ------------------------------------------------------------ worker events */
let pollTimer = null;
function startPolling() { if (!pollTimer) pollTimer = setInterval(poll, 400); poll(); }
async function poll() {
  let r; try { r = await api("/api/poll"); } catch (e) { return; }
  for (const ev of r.events) handle(ev);
  if (!r.busy && !r.events.length && !S.busy) { clearInterval(pollTimer); pollTimer = null; }
}
function handle(ev) {
  switch (ev.kind) {
    case "step": setStep(ev.idx, ev.detail, ev.pct); break;
    case "clear_rows": S.rows = []; refreshTree(); break;
    case "row": S.rows[ev.i] = ev.seg; refreshTree(); break;
    case "update_km": if (S.rows[ev.i]) { S.rows[ev.i].km = ev.km; refreshTree(); } break;
    case "trimmed": S.videoName = ev.name; $("fileLbl").textContent = shorten(ev.name); S.ver++; loadVideo(curPath(), 0, false); break;
    case "analyzed":
      Object.assign(S, {segments: ev.segs, total: ev.total, busy: false, sel: null, dirty: false, projDirty: true, rows: []});
      S.undo = []; S.redo = []; refreshTree(); loadPanel(); fitZoom(); updateButtons();
      if (sets.pause) setStep(2, "Translation is ready. Edit the lines on the timeline, then press 'Make dubbed video'.", 60);
      else renderNow();
      break;
    case "done": {
      S.busy = false; S.dubbed = true; S.saved = false; S.savedOnce = false; S.dirty = false; S.ver++;
      const pos = V.currentTime || 0; $("fileLbl").textContent = shorten(ev.name); updateButtons();
      setStep(4, "Done! Press 'Save video...' to keep it (it is not saved yet)." + ev.note, 100);
      setMode("dubbed"); setTimeout(() => loadVideo(curPath(), pos, true), 200); break; }
    case "cancelled": finishIdle("Cancelled."); break;
    case "error": finishIdle("Failed."); info("Something went wrong", ev.text); break;
    case "installed": info("Installed", "Done! Please stop the server (Ctrl+C), start it again with 'python app.py', then reload this page.");
      $("installBtn").textContent = "Installed - restart app"; break;
    case "install_failed": $("installBtn").disabled = false; $("installBtn").textContent = "Install now";
      info("Install failed", "Could not install automatically. Open a terminal and run:\n\npip install faster-whisper edge-tts deep-translator imageio-ffmpeg\n\n" + ev.text); break;
  }
}
function finishIdle(text) { S.busy = false; updateButtons(); setStep(-1, text, 0); }

/* ------------------------------------------------------------ warnings */
function showProblems() {
  const p = S.cfg.problems;
  $("warn").hidden = !p.messages.length; $("warnText").textContent = p.messages.join("\n");
  $("installBtn").hidden = !p.can_install;
}
$("installBtn").onclick = async () => { $("installBtn").disabled = true; $("installBtn").textContent = "Installing..."; await api("/api/install", {}); startPolling(); };

/* ------------------------------------------------------------ keys, drag & drop */
const typing = () => { const e = document.activeElement; return e && ["TEXTAREA", "INPUT", "SELECT"].includes(e.tagName) && e.type !== "range"; };
document.addEventListener("keydown", (e) => {
  if (!$("modal").hidden) return;
  if (e.ctrlKey && (e.key === "s" || e.key === "S")) { e.preventDefault(); saveProject(); return; }
  if (e.ctrlKey && (e.key === "o" || e.key === "O")) { e.preventDefault(); loadLater(); return; }
  if (typing()) return;
  if (e.key === " ") { if (["BUTTON"].includes(document.activeElement.tagName)) return; e.preventDefault(); togglePlay(); }
  else if (e.key === "Delete") doDelete();
  else if ((e.key === "s" || e.key === "S") && !e.ctrlKey) doSplit();
  else if (e.ctrlKey && e.key === "z") { e.preventDefault(); doUndo(); }
  else if (e.ctrlKey && (e.key === "y" || e.key === "Z")) { e.preventDefault(); doRedo(); }
});
const loadLater = () => loadProject();
let dragN = 0;
window.addEventListener("dragenter", (e) => { if (e.dataTransfer && [...e.dataTransfer.types].includes("Files")) { dragN++; $("dragVeil").hidden = false; } });
window.addEventListener("dragleave", () => { if (--dragN <= 0) { dragN = 0; $("dragVeil").hidden = true; } });
window.addEventListener("dragover", (e) => e.preventDefault());
window.addEventListener("drop", (e) => {
  e.preventDefault(); dragN = 0; $("dragVeil").hidden = true;
  const f = e.dataTransfer.files[0]; if (!f || S.busy) return;
  f.name.toLowerCase().endsWith(".khdub") ? loadProject(f) : begin(f);
});
window.addEventListener("beforeunload", (e) => { if ((S.segments.length && S.dirty && S.projDirty) || (S.dubbed && !S.saved)) { e.preventDefault(); e.returnValue = ""; } });

/* ------------------------------------------------------------ start */
(async function init() {
  S.cfg = await api("/api/config");
  S.cfg.steps.forEach((t) => { const d = document.createElement("div"); d.textContent = "○  " + t; $("steps").appendChild(d); });
  buildSidebar(); buildPanel(); showProblems();
  $("chooseBtn").onclick = chooseVideo; $("saveBtn").onclick = saveCopy; $("folderBtn").onclick = openFolder;
  $("renderBtn").onclick = renderNow; $("cancelBtn").onclick = cancel; $("playBtn").onclick = togglePlay;
  $("modeDub").onclick = () => switchSource("dubbed"); $("modeOrig").onclick = () => switchSource("original");
  $("undoBtn").onclick = doUndo; $("redoBtn").onclick = doRedo; $("splitBtn").onclick = doSplit; $("mergeBtn").onclick = doMerge;
  $("delBtn").onclick = doDelete; $("sentBtn").onclick = doSplitLines; $("addBtn").onclick = doAdd; $("srtBtn").onclick = exportSrt;
  $("drop").onclick = () => { if (!$("drop").hidden) chooseVideo(); };
  setStep(-1, "Choose a video to start. Nothing is saved until you press 'Save video...'.", 0);
  if (COARSE) $("dropSub").innerHTML = "Tap here to choose a video<br>MP4 &middot; MOV &middot; MKV &middot; AVI &middot; WEBM";
  updateButtons(); drawTimeline(); setInterval(tick, 100);
  const st = await api("/api/poll"); if (st.busy) { S.busy = true; startPolling(); }
})();
'''


@app.route("/static/style.css")
def _css():
    return Response(STYLE_CSS, mimetype="text/css")


@app.route("/static/app.js")
def _js():
    return Response(APP_JS, mimetype="application/javascript")

# ------------------------------------------------------------------ pages
@app.route("/")
def index():
    get_session()
    return render_template_string(INDEX_HTML).replace("__V__", str(BOOT))


@app.route("/api/config")
def config():
    get_session()
    return jsonify(voices=list(VOICES), accuracy=list(ACCURACY), speeds=SPEEDS, steps=STEPS,
                   khmer_font=KHMER_FONT, problems=problems())


def problems():
    out, can_install = [], False
    need = missing_packages()
    if need:
        out.append("Missing Python packages: " + ", ".join(need))
        can_install = True
    if not find_ffmpeg():
        out.append("FFmpeg was not found. Click 'Install now' and the app will download "
                   "its own copy (no PATH setup needed).")
        can_install = True
    return dict(messages=out, can_install=can_install)


@app.route("/api/install", methods=["POST"])
def install():
    s = get_session()
    need = missing_packages()
    if not find_ffmpeg() and "imageio-ffmpeg" not in need:
        need.append("imageio-ffmpeg")
    if not need:
        return jsonify(ok=True)

    def work():
        try:
            subprocess.run([sys.executable, "-m", "pip", "install", *need],
                           check=True, capture_output=True)
            s.post("installed")
        except Exception as e:
            s.post("install_failed", str(e))

    threading.Thread(target=work, daemon=True).start()
    return jsonify(ok=True)


# ----------------------------------------------------------- start a video
@app.route("/api/begin", methods=["POST"])
def begin():
    s = get_session()
    if s.busy:
        return jsonify(error="Busy"), 409
    need = missing_packages()
    if need:
        return jsonify(error="Some parts are missing: " + ", ".join(need) +
                       "\n\nClick 'Install now' in the yellow bar."), 400
    if not find_ffmpeg():
        return jsonify(error="FFmpeg (the video tool) was not found.\n\nClick the 'Install now' "
                             "button in the yellow bar, then restart the app."), 400
    keep = parse_range(request.form.get("range", ""))
    if keep is False:
        return jsonify(error="Please type it like 10:00-20:00 (or leave it empty)."), 400
    trim = keep if (keep[0] > 0 or keep[1] is not None) else None
    f = request.files.get("video")
    if not f or not f.filename:
        return jsonify(error="No video received."), 400
    st = json.loads(request.form.get("settings") or "{}")
    name = os.path.basename(f.filename.replace("\\", "/")) or "video.mp4"
    updir = os.path.join(s.workdir, "uploads", uuid.uuid4().hex[:8])
    os.makedirs(updir, exist_ok=True)
    path = os.path.join(updir, name)
    f.save(path)
    clean_stale(s.workdir)

    s.video_path, s.dubbed_path, s.project_path = path, None, None
    s.settings = st
    s.busy = True
    s.t0 = time.time()
    s.pipe.cancel_flag.clear()
    s.pipe.done_note = ""
    s.post("step", 0, "Starting...", 0)
    threading.Thread(
        target=s.pipe._guard, daemon=True,
        args=(s.pipe._trim_and_analyze, path, trim, ACCURACY[st.get("accuracy", "Balanced")],
              bool(st.get("remember")), st.get("engine", "Microsoft").lower(),
              bool(st.get("auto_voice", True)))).start()
    return jsonify(ok=True, name=name, trimmed=bool(trim))


@app.route("/api/cancel", methods=["POST"])
def cancel():
    get_session().pipe.cancel_flag.set()
    return jsonify(ok=True)


# ------------------------------------------------------------------ events
@app.route("/api/poll")
def poll():
    s = get_session()
    events = []
    try:
        while True:
            kind, a = s.msgs.get_nowait()
            if kind == "step":
                idx, detail, pct = a
                el = fmt_time(time.time() - s.t0)
                events.append(dict(kind="step", idx=idx, pct=pct,
                                   detail=f"{detail}     (time used: {el})"))
            elif kind == "row":
                events.append(dict(kind="row", i=a[0], seg=a[1]))
            elif kind == "update_km":
                events.append(dict(kind="update_km", i=a[0], km=a[1]))
            elif kind == "clear_rows":
                events.append(dict(kind="clear_rows"))
            elif kind == "trimmed":
                s.video_path = a[0]
                events.append(dict(kind="trimmed", name=os.path.basename(a[0])))
            elif kind == "analyzed":
                s.busy = False
                events.append(dict(kind="analyzed", segs=a[0], total=a[1]))
            elif kind == "done":
                s.busy = False
                s.dubbed_path = a[0]
                events.append(dict(kind="done", name=os.path.basename(a[0]), note=s.pipe.done_note))
            elif kind in ("cancelled",):
                s.busy = False
                events.append(dict(kind="cancelled"))
            elif kind == "error":
                s.busy = False
                events.append(dict(kind="error", text=a[0]))
            elif kind == "installed":
                events.append(dict(kind="installed"))
            elif kind == "install_failed":
                events.append(dict(kind="install_failed", text=a[0]))
    except queue.Empty:
        pass
    return jsonify(events=events, busy=s.busy)


# --------------------------------------------------------- editing helpers
@app.route("/api/split_lines", methods=["POST"])
def api_split_lines():
    segs = request.get_json()["segs"]
    return jsonify(segs=split_lines(segs))


@app.route("/api/translate", methods=["POST"])
def api_translate():
    d = request.get_json()
    try:
        return jsonify(km=translate_one(d["text"], (d.get("engine") or "microsoft").lower()))
    except Exception as e:
        return jsonify(error=Pipeline._friendly(e)), 500


@app.route("/api/preview", methods=["POST"])
def api_preview():
    s = get_session()
    d = request.get_json()
    vid = VOICES.get(d.get("voice") or "", VOICES[d.get("default_voice") or list(VOICES)[0]])
    path = os.path.join(s.workdir, "preview_%d.mp3" % int(time.time() * 1000))
    try:
        import asyncio
        import edge_tts
        asyncio.run(edge_tts.Communicate(d["text"], vid).save(path))
    except Exception as e:
        return jsonify(error=Pipeline._friendly(e)), 500
    return send_file(path, mimetype="audio/mpeg")


@app.route("/api/srt", methods=["POST"])
def api_srt():
    segs = request.get_json()["segs"]
    return jsonify(text=to_srt(segs))


@app.route("/api/srt_file", methods=["POST"])
def api_srt_file():
    segs = json.loads(request.form["segs"])
    name = request.form.get("name") or "video_khmer.srt"
    data = to_srt(segs).encode("utf-8-sig")                  # BOM: Khmer shows right
    return send_file(io.BytesIO(data), mimetype="application/x-subrip", as_attachment=True,
                     download_name=name)


# ------------------------------------------------------------------ render
@app.route("/api/render", methods=["POST"])
def render():
    s = get_session()
    d = request.get_json()
    if s.busy or not s.video_path:
        return jsonify(error="Busy or no video."), 409
    fixed = split_lines(d["segs"])                  # safety: never dub a multi-line box
    segs = copy.deepcopy(fixed)
    if not any((x.get("km") or "").strip() and x.get("km") != "..." and not x.get("mute")
               for x in segs):
        return jsonify(error="There is no Khmer text to turn into a voice.",
                       title="Nothing to voice", segs=fixed), 400
    if missing_packages() or not find_ffmpeg():
        return jsonify(error="Something is missing. Use 'Install now' in the yellow bar."), 400
    st = d["settings"]
    s.settings = st
    s.render_no += 1
    base = os.path.splitext(os.path.basename(s.video_path))[0]
    o = dict(video=s.video_path, voice=VOICES[st["voice"]],
             orig_pct=int(round(float(st["sound"]))), remove_voice=bool(st["novoice"]),
             install_demucs=bool(d.get("install_demucs")), shift=round(float(st["shift"]), 1),
             burn=bool(st["burn"]), segs=segs, total=float(d["total"]),
             out=os.path.join(s.workdir, f"{base}_khmer{s.render_no}.mp4"))
    s.pipe.done_note = ""
    s.pipe.cancel_flag.clear()
    s.t0 = time.time()
    s.busy = True
    s.post("step", 2, "Starting...", 60)
    threading.Thread(target=s.pipe._guard, args=(s.pipe._render, o), daemon=True).start()
    return jsonify(ok=True, segs=fixed, changed=len(fixed) != len(d["segs"]))


@app.route("/api/has_demucs")
def has_demucs():
    return jsonify(has=has_module("demucs"))


# ------------------------------------------------------------------- media
def _serve(path):
    if not path or not os.path.exists(path):
        return Response("Not found", 404)
    mt = mimetypes.guess_type(path)[0] or "video/mp4"
    return send_file(path, mimetype=mt, conditional=True)


@app.route("/media/original")
def media_original():
    return _serve(get_session().video_path)


@app.route("/media/dubbed")
def media_dubbed():
    return _serve(get_session().dubbed_path)


@app.route("/api/open_folder", methods=["POST"])
def api_open_folder():
    """Works when the server runs on your own computer: opens your Downloads folder."""
    try:
        open_folder(os.path.join(os.path.expanduser("~"), "Downloads", "x"))
    except Exception:
        pass
    return jsonify(ok=True)


@app.route("/api/download")
def download():
    s = get_session()
    if not s.dubbed_path:
        return Response("Not ready", 404)
    base = os.path.splitext(os.path.basename(request.args.get("name") or "video"))[0]
    return send_file(s.dubbed_path, mimetype="video/mp4", as_attachment=True,
                     download_name=base + "_khmer.mp4")


# ----------------------------------------------------------------- projects
def clip_keys(segs, voice_name):
    default = VOICES[voice_name]
    keys = set()
    for sg in segs:
        text = (sg.get("km") or "").strip()
        if not text or text == "..." or sg.get("mute"):
            continue
        vid = VOICES.get(sg.get("voice") or "", default)
        keys.add(hashlib.md5((vid + "|" + text).encode("utf-8")).hexdigest()[:16])
    return keys


@app.route("/api/project/save", methods=["POST"])
def project_save():
    s = get_session()
    d = json.loads(request.form["data"])
    segs, st = d["segs"], d["settings"]
    if not segs or not s.video_path:
        return jsonify(error="Nothing to save."), 400
    data = dict(version=1, video=os.path.abspath(s.video_path), total=d.get("total", 0),
                segs=segs,
                settings=dict(voice=st["voice"], sound=st["sound"], shift=st["shift"],
                              engine=st["engine"], accuracy=st["accuracy"],
                              novoice=st["novoice"], burn=st["burn"],
                              auto_voice=st["auto_voice"], pause=st["pause"]))
    files = {}
    for k in clip_keys(segs, st["voice"]):
        for ext in ("mp3", "none"):
            fp = os.path.join(s.workdir, f"c_{k}.{ext}")
            if os.path.exists(fp):
                files[f"clips/c_{k}.{ext}"] = fp
    with_video = bool(d.get("with_video")) and s.dubbed_path and os.path.exists(s.dubbed_path)
    if with_video:
        files["dubbed.mp4"] = s.dubbed_path
    data["has_video"] = bool(with_video)
    out = os.path.join(s.workdir, "project_out.khdub")
    write_project(out, data, files)
    base = os.path.splitext(os.path.basename(s.video_path))[0]
    return send_file(out, mimetype="application/octet-stream", as_attachment=True,
                     download_name=base + ".khdub")


@app.route("/api/project/load", methods=["POST"])
def project_load():
    s = get_session()
    if s.busy:
        return jsonify(error="Busy"), 409
    f = request.files.get("project")
    if not f:
        return jsonify(error="No file."), 400
    tmp = os.path.join(s.workdir, "incoming.khdub")
    f.save(tmp)
    try:
        d = read_project(tmp, s.workdir)
        segs = d["segs"]
    except Exception as e:
        return jsonify(error="This file could not be opened.\n\n" + str(e)), 400
    clean_stale(s.workdir)
    video = d.get("video") or ""
    found = os.path.exists(video)
    loaded = os.path.join(s.workdir, "loaded_dubbed.mp4")
    has_dub = bool(d.get("has_video") and os.path.exists(loaded))
    s.project_path = tmp
    s.pending_project = d
    s.video_path = video if found else None
    s.dubbed_path = loaded if has_dub else None
    return jsonify(ok=True, segs=segs, total=float(d.get("total") or 0),
                   settings=d.get("settings") or {}, video_found=found,
                   name=os.path.basename(video), has_dubbed=has_dub)


@app.route("/api/project/video", methods=["POST"])
def project_video():
    s = get_session()
    f = request.files.get("video")
    if not f:
        return jsonify(error="No video."), 400
    name = os.path.basename(f.filename.replace("\\", "/")) or "video.mp4"
    updir = os.path.join(s.workdir, "uploads", uuid.uuid4().hex[:8])
    os.makedirs(updir, exist_ok=True)
    path = os.path.join(updir, name)
    f.save(path)
    s.video_path = path
    return jsonify(ok=True, name=name)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "5000"))
    print(f"Khmer Dubber Editor  ->  http://127.0.0.1:{port}")
    app.run(host=os.environ.get("HOST", "127.0.0.1"), port=port, threaded=True, debug=False)
