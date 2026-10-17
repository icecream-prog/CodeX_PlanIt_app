"""
Schedule Planner (PlanIt) -  night-drive edition  (v4)
==============================================
A schedule information system with reminders, loud alarms and a moving
video background.

Setup (one time):
    pip install pillow opencv-python
Run:
    python schedule_system.py
    (keep background.mp4 - or any .mp4 / space.jpg - in the same folder)

New in this version
  * VIDEO BACKGROUND: plays your clip on a loop behind the app
    (decoded in a background thread, so the window stays smooth)
  * Panels glide in at start and slide away / back with "View scenery"
  * Livelier buttons: glow on hover, ripple flash on click, header buttons
    lift up, the main button breathes
  * Settings: choose another video or picture, smoothness (15 / 24 / 30 fps),
    switch the animation off to save battery (it also pauses when minimised)
  * Night-drive colour theme to match the video

Everything from before is still here: loud long alarms, 10 sounds, per-schedule
sounds, snooze, undo, filters, calendar picker, and a layout that adapts to any
screen size.

Shortcuts:  Enter = save   Del = delete   Ctrl+N = new   Ctrl+F = search
            Esc = cancel edit / leave fullscreen   F11 = fullscreen
"""

import array
import calendar
import json
import math
import os
import random
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import uuid
import wave
from datetime import date, datetime, timedelta
from datetime import time as dtime
from tkinter import filedialog, ttk

try:
    from PIL import Image, ImageDraw, ImageOps, ImageTk
    HAS_PIL = True
    RESAMPLE = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
except ImportError:
    HAS_PIL = False

try:
    import cv2
    HAS_CV2 = True
except ImportError:
    HAS_CV2 = False

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SAVE_FILE = os.path.join(BASE_DIR, "schedules.json")
SETTINGS_FILE = os.path.join(BASE_DIR, "settings.json")

VIDEO_EXT = (".mp4", ".mov", ".m4v", ".avi", ".mkv", ".webm")
IMAGE_EXT = (".jpg", ".jpeg", ".png", ".bmp", ".webp")

DT_FORMAT = "%Y-%m-%d %H:%M"
SNOOZE_FORMAT = "%Y-%m-%d %H:%M:%S"
MISSED_AFTER_MIN = 60   # app was closed and the schedule is this late -> don't ring
FILTERS = ["All", "Today", "Upcoming", "Overdue", "Done"]

# ---------------------------------------------------------------- colors (night drive)
BG = "#070a14"
CARD = "#0c1322"
TABLE_BG = "#0e1729"
INPUT = "#16213a"
EDGE = "#26355a"
TEXT = "#e8eeff"
MUTED = "#8fa0c8"
FAINT = "#586a94"
ACCENT = "#2f7bff"
BTN = "#1f2b4d"
DANGER = "#c0405e"
GOLD = "#ffd877"
GLOW = "#a9c8ff"
GLASS_TINT = (9, 15, 30)
GLASS_EDGE = (60, 100, 190)


def hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def mix(c1, c2, t):
    a, b = hex_to_rgb(c1), hex_to_rgb(c2)
    return "#%02x%02x%02x" % tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def short_span(secs):
    d, rem = divmod(int(secs), 86400)
    h, rem = divmod(rem, 3600)
    m, s = divmod(rem, 60)
    if d:
        return f"{d}d {h}h"
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m {s:02d}s"
    return f"{s}s"


# ================================================================ responsive layout maths
def compute_layout(W, H, sc=1.0):
    """Decide how the window is arranged for a given size.  Pure function (easy to test).

    wide     >= 860 px : form on the left, schedule list on the right
    compact  <  860 px : one panel at a time, switched with the tab buttons
    tiny     <  480 px : same as compact with smaller header and icon-only tabs
    """
    px = lambda n: int(n * sc)
    compact = W < px(860)
    tiny = W < px(480)
    mode = "tiny" if tiny else ("compact" if compact else "wide")
    m = px(12) if tiny else (px(18) if compact else px(22))
    gap = px(18)
    top = px(108) if compact else px(96)
    bottom = max(top + px(120), H - px(40))
    if compact:
        left = right = (m, top, max(m + 50, W - m), bottom)
    else:
        lw = max(px(300), min(px(360), int(W * 0.30)))
        left = (m, top, m + lw, bottom)
        right = (m + lw + gap, top, max(m + lw + gap + 50, W - m), bottom)
    return {"mode": mode, "compact": compact, "tiny": tiny, "m": m, "gap": gap,
            "top": top, "bottom": bottom, "left": left, "right": right}


# ================================================================ moving background
def find_media(folder):
    """Return (video_path, image_path) found in a folder ('' when none).
    Files whose name starts with 'background' win; otherwise the first match."""
    try:
        names = sorted(n for n in os.listdir(folder) if not n.startswith("."))
    except OSError:
        return "", ""

    def pick(exts):
        hits = [n for n in names if os.path.splitext(n)[1].lower() in exts]
        first = [n for n in hits if n.lower().startswith("background")] or hits
        return os.path.join(folder, first[0]) if first else ""

    return pick(VIDEO_EXT), pick(IMAGE_EXT)


def cover_fit(img, size):
    """Scale a PIL image so it fills `size`, cropping the overflow (like CSS 'cover')."""
    W, H = size
    iw, ih = img.size
    s = max(W / iw, H / ih)
    nw, nh = max(W, int(iw * s + 0.999)), max(H, int(ih * s + 0.999))
    img = img.resize((nw, nh), RESAMPLE)
    l, t = (nw - W) // 2, (nh - H) // 2
    return img.crop((l, t, l + W, t + H))


class ImageSource:
    """A still picture used as the background."""
    static = True
    fps = 0

    def __init__(self, path):
        self.img = Image.open(path).convert("RGB")
        self._size = None
        self._cache = None

    def read(self, size):
        if self._size != size:
            self._cache, self._size = cover_fit(self.img, size), size
        return self._cache.copy()

    def current(self, size):
        return self.read(size)

    def skip(self):
        pass

    def close(self):
        pass


class VideoSource:
    """A looping video decoded with OpenCV; frames are cropped to fill the window."""
    static = False

    def __init__(self, path):
        self.cap = cv2.VideoCapture(path)
        if not self.cap.isOpened():
            raise RuntimeError("cannot open video")
        fps = self.cap.get(cv2.CAP_PROP_FPS) or 30.0
        self.fps = fps if 1 <= fps <= 240 else 30.0
        self.last = None

    def skip(self):
        self.cap.grab()

    def read(self, size):
        """Decode the next frame (looping at the end) and fit it to `size`."""
        ok, frame = self.cap.read()
        if not ok:   # end of clip -> loop
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
            ok, frame = self.cap.read()
            if not ok:
                return None
        self.last = frame
        return self._fit(frame, size)

    def current(self, size):
        """Re-fit the frame already on screen (used while paused / resizing)."""
        return self._fit(self.last, size) if self.last is not None else self.read(size)

    @staticmethod
    def _fit(frame, size):
        W, H = size
        h, w = frame.shape[:2]
        s = max(W / w, H / h)
        nw, nh = max(W, int(w * s + 0.999)), max(H, int(h * s + 0.999))
        interp = cv2.INTER_AREA if s < 0.45 else cv2.INTER_LINEAR   # LINEAR is 2x faster
        frame = cv2.resize(frame, (nw, nh), interpolation=interp)
        l, t = (nw - W) // 2, (nh - H) // 2
        frame = frame[t:t + H, l:l + W]
        return Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))

    def close(self):
        self.cap.release()


class Overlay:
    """Caches the frosted-glass panels and the dark header/footer fades,
    so adding them to a frame costs only a couple of milliseconds."""

    def __init__(self):
        self._glass = {}
        self._fade = {}

    def glass(self, w, h):
        key = (w, h)
        if key not in self._glass:
            if len(self._glass) > 8:
                self._glass.clear()
            alpha = Image.new("L", (w, h), 0)
            ImageDraw.Draw(alpha).rounded_rectangle((0, 0, w - 1, h - 1), radius=18, fill=205)
            rgb = Image.new("RGB", (w, h), GLASS_TINT)
            d = ImageDraw.Draw(rgb)
            d.rounded_rectangle((0, 0, w - 1, h - 1), radius=18, outline=GLASS_EDGE, width=1)
            ImageDraw.Draw(alpha).rounded_rectangle((0, 0, w - 1, h - 1), radius=18,
                                                    outline=255, width=1)
            self._glass[key] = (rgb, alpha)
        return self._glass[key]

    def fade_masks(self, W, top, bottom):
        key = (W, top, bottom)
        if key not in self._fade:
            if len(self._fade) > 8:
                self._fade.clear()
            grad = Image.linear_gradient("L")   # 256x256, black (top) -> white (bottom)
            strength = lambda v: int(v * 0.62)
            self._fade[key] = (
                ImageOps.flip(grad).resize((W, max(1, top))).point(strength),
                grad.resize((W, max(1, bottom))).point(strength),
            )
        return self._fade[key]

    def apply(self, frame, boxes, top, bottom):
        W, H = frame.size
        top_mask, bot_mask = self.fade_masks(W, top, bottom)
        frame.paste((4, 8, 18), (0, 0, W, top_mask.size[1]), top_mask)
        frame.paste((4, 8, 18), (0, H - bot_mask.size[1], W, H), bot_mask)
        for x0, y0, x1, y1 in boxes:
            w, h = x1 - x0, y1 - y0
            if w < 20 or h < 20 or y0 >= H or y1 <= 0:
                continue
            rgb, alpha = self.glass(w, h)
            frame.paste(rgb, (x0, y0), alpha)   # PIL clips anything outside the frame


class BackgroundEngine:
    """Produces ready-to-show background frames on a worker thread.

    The Tk window only has to copy the newest frame onto the canvas, so the
    interface never waits for video decoding.
    """

    def __init__(self, source, fps=24):
        self.source = source
        self.overlay = Overlay()
        self.lock = threading.Lock()
        self.wake = threading.Event()
        self.stop_ev = threading.Event()
        self.size = (0, 0)
        self.boxes = []
        self.top = self.bottom = 0
        self.dirty = True
        self.paused = False
        self.fps = fps
        self.latest = None
        self.fresh = False
        self.frames = 0
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    # ---- called from the Tk thread
    def set_view(self, size, boxes, top, bottom):
        with self.lock:
            self.size, self.boxes, self.top, self.bottom = size, list(boxes), top, bottom
            self.dirty = True
        self.wake.set()

    def set_fps(self, fps):
        self.fps = max(5, min(60, int(fps)))

    def set_paused(self, paused):
        self.paused = bool(paused)
        self.wake.set()

    def take(self):
        with self.lock:
            if not self.fresh:
                return None
            self.fresh = False
            return self.latest

    def stop(self):
        self.stop_ev.set()
        self.wake.set()
        self.thread.join(timeout=1.5)
        try:
            self.source.close()
        except Exception:
            pass

    # ---- worker thread
    def _render(self, advance=True):
        with self.lock:
            size, boxes, top, bottom = self.size, list(self.boxes), self.top, self.bottom
            self.dirty = False
        if size[0] < 50 or size[1] < 50:
            return
        try:
            frame = self.source.read(size) if advance else self.source.current(size)
        except Exception:
            frame = None
        if frame is None:
            return
        self.overlay.apply(frame, boxes, top, bottom)
        with self.lock:
            self.latest, self.fresh = frame, True
        self.frames += 1

    def _run(self):
        next_t = time.perf_counter()
        while not self.stop_ev.is_set():
            if self.source.static or self.paused:
                # nothing is playing: just redraw when the window or the panels changed
                self.wake.wait(0.25)
                self.wake.clear()
                next_t = time.perf_counter()
                if self.stop_ev.is_set():
                    break
                if self.dirty:
                    self._render(advance=False)
                    self.stop_ev.wait(0.016)    # coalesce rapid updates (e.g. panel slide)
                continue
            step = max(1, round(self.source.fps / self.fps))   # e.g. 30 fps clip shown at 15 fps
            for _ in range(step - 1):
                self.source.skip()
            self._render(advance=True)
            next_t += 1.0 / self.fps
            delay = next_t - time.perf_counter()
            if delay > 0:
                self.stop_ev.wait(delay)
            elif delay < -0.25:           # fell behind: don't try to catch up
                next_t = time.perf_counter()


# ================================================================ alarm sounds
RATE = 22050
SOUND_NAMES = ["Classic Beeps", "Digital Clock", "Siren", "Police Two-Tone",
               "Emergency Pulse", "Church Bell", "Chime Melody", "Morning Melody",
               "Buzzer", "Sonar Ping"]
CUSTOM = "Custom file"
SYSTEM = "System beep"
ALL_SOUNDS = SOUND_NAMES + [CUSTOM, SYSTEM]

DEFAULT_SETTINGS = {
    "alarm_sound": "Siren",
    "reminder_sound": "Chime Melody",
    "volume": 100,
    "ring_seconds": 120,     # 0 = until I stop it
    "snooze_min": 5,
    "custom_path": "",
    "background": "",        # '' = automatic (background.mp4 / any video / space.jpg)
    "bg_play": True,
    "bg_fps": 24,
    "idle_hide": 60,         # seconds without input before the panels slide away (0 = never)
}
RING_CHOICES = [("30 seconds", 30), ("1 minute", 60), ("2 minutes", 120),
                ("5 minutes", 300), ("10 minutes", 600), ("Until I stop it", 0)]
SNOOZE_CHOICES = [1, 5, 10, 15, 30]
FPS_CHOICES = [("Battery saver · 15 fps", 15), ("Balanced · 24 fps", 24), ("Smooth · 30 fps", 30)]
IDLE_CHOICES = [("Never", 0), ("After 15 seconds", 15), ("After 30 seconds", 30),
                ("After 1 minute", 60), ("After 5 minutes", 300)]


def _silence(d):
    return [0.0] * int(RATE * d)


def _tone(freq, dur, shape="square", decay=0.0, fade=0.004):
    n = int(RATE * dur)
    w = 2 * math.pi * freq / RATE
    fn = max(1, int(RATE * fade))
    out = []
    for i in range(n):
        s = math.sin(w * i)
        if shape == "square":
            v = 1.0 if s >= 0 else -1.0
        elif shape == "soft":
            v = 0.65 * s + 0.35 * (1.0 if s >= 0 else -1.0)
        else:
            v = s
        env = min(1.0, i / fn, (n - i) / fn)
        if decay:
            env *= math.exp(-decay * i / RATE)
        out.append(v * env)
    return out


def _sweep(f0, f1, dur):
    n = int(RATE * dur)
    ph, out = 0.0, []
    for i in range(n):
        ph += 2 * math.pi * (f0 + (f1 - f0) * i / n) / RATE
        out.append(1.0 if math.sin(ph) >= 0 else -1.0)
    return out


def _bell(freq, dur):
    parts = [(1.0, 1.0, 2.2), (2.0, 0.6, 3.2), (2.76, 0.5, 4.0), (5.4, 0.3, 6.0), (8.93, 0.15, 8.0)]
    out = []
    for i in range(int(RATE * dur)):
        t = i / RATE
        out.append(sum(a * math.sin(2 * math.pi * freq * m * t) * math.exp(-d * t)
                       for m, a, d in parts))
    return out


def build_samples(name):
    """One cycle of the sound (a few seconds); the player loops it."""
    if name == "Classic Beeps":
        return (_tone(1000, .18) + _silence(.12)) * 4 + _silence(.5)
    if name == "Digital Clock":
        group = (_tone(2400, .07) + _silence(.07)) * 4
        return group + _silence(.25) + group + _silence(.7)
    if name == "Siren":
        return (_sweep(650, 1400, .9) + _sweep(1400, 650, .9)) * 2
    if name == "Police Two-Tone":
        return (_tone(960, .38) + _tone(1280, .38)) * 3
    if name == "Emergency Pulse":
        return (_tone(1800, .06) + _silence(.06)) * 10 + _silence(.45)
    if name == "Church Bell":
        return _bell(660, 1.9) + _bell(660, 1.9)
    if name == "Chime Melody":
        notes = []
        for f in (523, 659, 784, 1047):
            notes += _tone(f, .3, "sine", decay=3.5)
        return notes + _silence(.7)
    if name == "Morning Melody":
        out = []
        for f, d in ((392, .18), (523, .18), (659, .18), (784, .36), (659, .18), (784, .5)):
            out += _tone(f, d, "soft", decay=1.5) + _silence(.04)
        return out + _silence(.6)
    if name == "Buzzer":
        return (_tone(240, .14) + _silence(.05)) * 7 + _silence(.4)
    if name == "Sonar Ping":
        return _tone(1400, .9, "sine", decay=4.5) + _silence(1.0)
    raise ValueError(name)


def write_wav(path, samples, volume):
    """Normalise to full scale, then apply the volume percentage."""
    peak = max(1e-9, max(abs(x) for x in samples))
    k = 32767 * 0.97 * (max(0, min(100, volume)) / 100.0) / peak
    data = array.array("h", (int(max(-32767, min(32767, x * k))) for x in samples))
    if sys.byteorder == "big":
        data.byteswap()
    with wave.open(path, "wb") as f:
        f.setnchannels(1)
        f.setsampwidth(2)
        f.setframerate(RATE)
        f.writeframes(data.tobytes())


class SoundBank:
    """Creates the .wav files on demand and caches them in a temp folder."""

    def __init__(self, folder=None):
        self.dir = folder or os.path.join(tempfile.gettempdir(), "schedule_planner_sounds")
        os.makedirs(self.dir, exist_ok=True)

    def path(self, name, volume):
        vol = int(volume)
        fn = os.path.join(self.dir, f"{name.replace(' ', '_').replace('-', '_')}_{vol}.wav")
        if not os.path.exists(fn):
            try:   # write to a temp name first so a half-written file is never played
                tmp = f"{fn}.{os.getpid()}.tmp"
                write_wav(tmp, build_samples(name), vol)
                os.replace(tmp, fn)
            except OSError:
                return None
        return fn


class SoundPlayer:
    """Loops a .wav for a set time without freezing the window.

    Windows: winsound (async + loop).  macOS: afplay.  Linux: paplay / aplay / sox / ffplay.
    Falls back to the system bell if nothing else is available.
    """

    def __init__(self, root):
        self.root = root
        self.is_win = sys.platform.startswith("win")
        self.cmd = None
        if not self.is_win:
            for cmd in (["afplay"], ["paplay"], ["aplay", "-q"], ["play", "-q"],
                        ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"]):
                if shutil.which(cmd[0]):
                    self.cmd = cmd
                    break
        self.proc = None
        self.job = None
        self.stop_job = None
        self.path = None
        self.loop = False
        self.active = False

    def play(self, path, loop=True, seconds=None):
        self.stop()
        self.active, self.path, self.loop = True, path, loop
        started = False
        if self.is_win and path:
            try:
                import winsound
                flags = winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT
                if loop:
                    flags |= winsound.SND_LOOP
                winsound.PlaySound(path, flags)
                started = True
            except Exception:
                started = False
        elif path and self.cmd:
            started = self._spawn()
        if not started:
            self._bell(0)
        if seconds:
            self.stop_job = self.root.after(int(seconds * 1000), self.stop)

    def _spawn(self):
        if not self.active:
            return True
        try:
            self.proc = subprocess.Popen(self.cmd + [self.path], stdout=subprocess.DEVNULL,
                                         stderr=subprocess.DEVNULL)
        except Exception:
            return False
        self.job = self.root.after(250, self._watch)
        return True

    def _watch(self):
        if not self.active:
            return
        if self.proc is not None and self.proc.poll() is None:
            self.job = self.root.after(250, self._watch)
        elif self.loop:
            if not self._spawn():
                self._bell(0)
        else:
            self.active = False

    def _bell(self, n):
        if not self.active:
            return
        if not self.loop and n >= 3:
            self.active = False
            return
        try:
            self.root.bell()
        except tk.TclError:
            pass
        self.job = self.root.after(500, self._bell, n + 1)

    def stop(self):
        self.active = False
        for j in (self.job, self.stop_job):
            if j:
                try:
                    self.root.after_cancel(j)
                except tk.TclError:
                    pass
        self.job = self.stop_job = None
        if self.is_win:
            try:
                import winsound
                winsound.PlaySound(None, winsound.SND_PURGE)
            except Exception:
                pass
        if self.proc is not None:
            try:
                self.proc.terminate()
            except Exception:
                pass
            self.proc = None


# ================================================================ widgets
class HoverButton(tk.Label):
    """An animated flat button.

    hover  : colour fades up and a soft glow ring appears
    click  : a bright ripple flash that fades away
    pulse  : (optional) the glow ring slowly "breathes" while idle
    on_hover(bool): optional callback, used to lift the header buttons
    """

    def __init__(self, parent, text="", command=None, bg=BTN, fg=TEXT,
                 font=("Helvetica", 10, "bold"), padx=14, pady=7,
                 pulse=False, on_hover=None, **kw):
        super().__init__(parent, text=text, bg=bg, fg=fg, font=font, padx=padx, pady=pady,
                         cursor="hand2", highlightthickness=2, highlightbackground=bg,
                         highlightcolor=bg, bd=0, **kw)
        self.command = command
        self.on_hover = on_hover
        self.base = bg
        self._bg = bg
        self._hl = bg
        self._job = None
        self._inside = False
        self._pulse = pulse
        self._t = random.random() * 6.28
        self.bind("<Enter>", self._enter)
        self.bind("<Leave>", self._leave)
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<ButtonRelease-1>", self._release)
        if pulse:
            self.after(120, self._pulse_step)

    # colours for the hovered state
    def _hover_bg(self):
        return mix(self.base, "#ffffff", 0.16)

    def _glow(self):
        return mix(self.base, GLOW, 0.75)

    def set_base(self, color):
        if color == self.base:
            return
        self.base = color
        self._anim(self._hover_bg() if self._inside else color,
                   self._glow() if self._inside else color)

    def _anim(self, bg, hl, steps=6, delay=14):
        if self._job:
            try:
                self.after_cancel(self._job)
            except tk.TclError:
                pass
        s_bg, s_hl = self._bg, self._hl

        def step(i=1):
            if not self.winfo_exists():
                return
            k = i / steps
            self._bg, self._hl = mix(s_bg, bg, k), mix(s_hl, hl, k)
            self.configure(bg=self._bg, highlightbackground=self._hl, highlightcolor=self._hl)
            self._job = self.after(delay, step, i + 1) if i < steps else None

        step()

    def _enter(self, _e):
        self._inside = True
        self._anim(self._hover_bg(), self._glow())
        if self.on_hover:
            self.on_hover(True)

    def _leave(self, _e):
        self._inside = False
        self._anim(self.base, self.base)
        if self.on_hover:
            self.on_hover(False)

    def _press(self, _e):
        self._anim(mix(self.base, "#000000", 0.3), self._glow(), steps=2, delay=10)

    def _release(self, _e):
        if self._inside:
            # ripple: flash bright, then fade back to the hover colour
            self._bg, self._hl = mix(self.base, "#ffffff", 0.6), "#ffffff"
            self.configure(bg=self._bg, highlightbackground=self._hl, highlightcolor=self._hl)
            self._anim(self._hover_bg(), self._glow(), steps=10, delay=16)
            if self.command:
                self.command()   # last: the command may destroy this widget

    def _pulse_step(self):
        if not self.winfo_exists():
            return
        if self._pulse and not self._inside and self._job is None:
            self._t += 0.16
            k = (math.sin(self._t) + 1) / 2
            self._hl = mix(self.base, GLOW, 0.1 + 0.65 * k)
            self.configure(highlightbackground=self._hl, highlightcolor=self._hl)
        self.after(50, self._pulse_step)


class ScrollFrame(tk.Frame):
    """A frame whose content scrolls (mouse wheel / scrollbar) when the window is small."""

    def __init__(self, parent, bg=CARD):
        super().__init__(parent, bg=bg)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0, yscrollincrement=20)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner = tk.Frame(self.canvas, bg=bg)
        self.win = self.canvas.create_window(0, 0, window=self.inner, anchor="nw")
        self._vsb_shown = False
        self.inner.bind("<Configure>", lambda e: self._update())
        self.canvas.bind("<Configure>", self._on_canvas)
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.bind_all(seq, self._wheel, add="+")

    def _on_canvas(self, e):
        self.canvas.itemconfigure(self.win, width=e.width)
        self._update()

    def _needs_scroll(self):
        return self.inner.winfo_reqheight() > self.canvas.winfo_height() + 1

    def _update(self):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        need = self._needs_scroll()
        if need and not self._vsb_shown:
            self.vsb.pack(side="right", fill="y")
            self._vsb_shown = True
        elif not need and self._vsb_shown:
            self.vsb.pack_forget()
            self._vsb_shown = False
            self.canvas.yview_moveto(0)

    def _wheel(self, e):
        try:
            if not self.winfo_exists() or not self._needs_scroll():
                return
            w = self.winfo_containing(e.x_root, e.y_root)
        except (tk.TclError, KeyError):
            return
        if isinstance(w, (tk.Listbox, tk.Text, ttk.Treeview)):
            return
        inside = False
        while w is not None:
            if w is self:
                inside = True
                break
            w = getattr(w, "master", None)
        if not inside:
            return
        if e.num == 4 or getattr(e, "delta", 0) > 0:
            self.canvas.yview_scroll(-2, "units")
        else:
            self.canvas.yview_scroll(2, "units")


class DatePicker(tk.Toplevel):
    """Small month calendar for choosing a date."""

    def __init__(self, app, initial, on_pick):
        super().__init__(app.root)
        self.title("Pick a date")
        self.configure(bg=CARD)
        self.resizable(False, False)
        self.transient(app.root)
        self.on_pick = on_pick
        self.selected = initial
        self.view = initial.replace(day=1)

        head = tk.Frame(self, bg=CARD)
        head.pack(fill="x", padx=12, pady=(12, 6))
        HoverButton(head, "‹", lambda: self.shift(-1), padx=10, pady=3).pack(side="left")
        self.month_lbl = tk.Label(head, bg=CARD, fg="white", width=14,
                                  font=("Helvetica", 12, "bold"))
        self.month_lbl.pack(side="left", expand=True)
        HoverButton(head, "›", lambda: self.shift(1), padx=10, pady=3).pack(side="right")

        self.grid_frame = tk.Frame(self, bg=CARD)
        self.grid_frame.pack(padx=12, pady=(0, 12))
        self.render()

        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        x = min(max(0, app.root.winfo_rootx() + 60), max(0, sw - self.winfo_reqwidth()))
        y = min(max(0, app.root.winfo_rooty() + 120), max(0, sh - self.winfo_reqheight() - 40))
        self.geometry(f"+{x}+{y}")
        self.focus_set()

    def shift(self, n):
        y, m = self.view.year, self.view.month + n
        if m < 1:
            y, m = y - 1, 12
        elif m > 12:
            y, m = y + 1, 1
        self.view = date(y, m, 1)
        self.render()

    def render(self):
        for w in self.grid_frame.winfo_children():
            w.destroy()
        self.month_lbl.configure(text=self.view.strftime("%B %Y"))
        for c, name in enumerate(["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"]):
            tk.Label(self.grid_frame, text=name, bg=CARD, fg=MUTED, width=4,
                     font=("Helvetica", 9, "bold")).grid(row=0, column=c, pady=(0, 4))
        today = date.today()
        weeks = calendar.Calendar(firstweekday=6).monthdayscalendar(
            self.view.year, self.view.month)
        for r, week in enumerate(weeks, start=1):
            for c, day in enumerate(week):
                if day == 0:
                    continue
                d = date(self.view.year, self.view.month, day)
                bg = ACCENT if d == self.selected else ("#2b4fa8" if d == today else BTN)
                HoverButton(self.grid_frame, str(day), lambda d=d: self.pick(d), bg=bg,
                            width=3, padx=2, pady=4, font=("Helvetica", 10)).grid(
                    row=r, column=c, padx=2, pady=2)

    def pick(self, d):
        self.on_pick(d.strftime("%Y-%m-%d"))
        self.destroy()


class AlarmPopup(tk.Toplevel):
    """Alarm window: pulses and rings for 'due', gentle chime for 'reminder'.
    Sizes itself to the screen, so it also fits small displays."""

    KINDS = {
        "reminder": ("Coming up soon", "⏳", "#ffc857", False),
        "due": ("It's time!", "⏰", "#ff5c7a", True),
        "snoozed": ("Snooze is over", "⏰", "#ff5c7a", True),
    }

    def __init__(self, app, sched, kind):
        super().__init__(app.root)
        self.app, self.sched, self.kind = app, sched, kind
        heading, icon, self.accent, self.loud = self.KINDS[kind]
        self.alive = True
        self.title("Schedule alarm")
        self.configure(bg=self.accent)
        self.resizable(False, False)
        try:
            self.attributes("-topmost", True)
            self.attributes("-alpha", 0.0)
        except tk.TclError:
            pass

        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        narrow = sw < 520
        wrap = max(160, min(320, sw - 110))

        body = tk.Frame(self, bg=CARD)
        body.pack(padx=3, pady=3)
        tk.Label(body, text=icon, bg=CARD, font=("Helvetica", 30 if sh < 600 else 34)).pack(pady=(14, 0))
        tk.Label(body, text=heading, bg=CARD, fg=self.accent,
                 font=("Helvetica", 17, "bold")).pack()
        tk.Label(body, text=sched["title"], bg=CARD, fg="white", wraplength=wrap,
                 font=("Helvetica", 14, "bold")).pack(padx=20, pady=(8, 2))
        self.info = tk.Label(body, bg=CARD, fg=MUTED, font=("Helvetica", 10), wraplength=wrap)
        self.info.pack()
        if sched["notes"]:
            tk.Label(body, text=sched["notes"], bg=CARD, fg=TEXT, wraplength=wrap,
                     font=("Helvetica", 10)).pack(padx=20, pady=(6, 0))
        self.ring_lbl = tk.Label(body, bg=CARD, fg=GOLD, font=("Helvetica", 10, "bold"))
        if self.loud:
            self.ring_lbl.pack(pady=(8, 0))

        row = tk.Frame(body, bg=CARD)
        row.pack(pady=14, padx=16, fill="x" if narrow else "none")
        side = "top" if narrow else "left"
        fill = "x" if narrow else "none"
        HoverButton(row, "Dismiss", self.close).pack(side=side, fill=fill, padx=4, pady=3)
        if self.loud:
            n = app.settings["snooze_min"]
            HoverButton(row, f"Snooze {n} min", self.snooze).pack(side=side, fill=fill, padx=4, pady=3)
        HoverButton(row, "Mark done", self.mark_done, bg=ACCENT, pulse=self.loud).pack(
            side=side, fill=fill, padx=4, pady=3)

        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())

        self.update_idletasks()
        r = app.root
        w, h = self.winfo_reqwidth(), self.winfo_reqheight()
        off = 28 * len(app.popups)
        x = r.winfo_rootx() + (r.winfo_width() - w) // 2 + off
        y = r.winfo_rooty() + (r.winfo_height() - h) // 2 + off
        x = max(0, min(x, sw - w))          # always keep it fully on screen
        y = max(0, min(y, sh - h - 40))
        self.geometry(f"+{x}+{y}")
        app.popups.append(self)

        secs = app.start_sound(sched, kind)
        self.ring_until = datetime.now() + timedelta(seconds=secs) if secs else None

        self._fade_in(0)
        self._update_info()
        if self.loud:
            self._pulse(0.0)

    def _fade_in(self, i):
        if not self.alive:
            return
        try:
            self.attributes("-alpha", min(0.97, i / 10))
        except tk.TclError:
            return
        if i < 10:
            self.after(25, self._fade_in, i + 1)

    def _update_info(self):
        if not self.alive:
            return
        dt = datetime.strptime(self.sched["when"], DT_FORMAT)
        if self.kind == "reminder":
            left = (dt - datetime.now()).total_seconds()
            self.info.configure(text=f"Starts in {short_span(left)}  ·  {dt:%H:%M}"
                                if left > 0 else f"It's {dt:%H:%M} — time to go!")
        else:
            self.info.configure(text=f"Scheduled for {dt:%A, %b %d  ·  %H:%M}")
        if self.loud:
            if self.app.player.active:
                if self.ring_until:
                    left = max(0, int((self.ring_until - datetime.now()).total_seconds()))
                    self.ring_lbl.configure(text=f"🔊 Ringing  ·  stops in {left // 60}:{left % 60:02d}")
                else:
                    self.ring_lbl.configure(text="🔊 Ringing until you stop it")
            else:
                self.ring_lbl.configure(text="🔇 Sound finished — dismiss or snooze")
        self.after(500, self._update_info)

    def _pulse(self, t):
        if not self.alive:
            return
        self.configure(bg=mix(self.accent, "#6a1230", (math.sin(t) + 1) / 2))
        self.after(50, self._pulse, t + 0.4)

    def snooze(self):
        n = self.app.settings["snooze_min"]
        until = datetime.now() + timedelta(minutes=n)
        self.sched["snooze_until"] = until.strftime(SNOOZE_FORMAT)
        self.app.save()
        self.app.toast(f"Snoozed until {until:%H:%M}")
        self.close()

    def mark_done(self):
        self.sched["done"] = True
        self.app.save()
        self.app.refresh_table()
        self.app.toast("Marked as done ✓")
        self.close()

    def close(self):
        self.alive = False
        if self in self.app.popups:
            self.app.popups.remove(self)
        self.destroy()
        self.app.popup_closed()


class SettingsDialog(tk.Toplevel):
    """Alarm sound, volume, ring length, snooze, background - sized to fit any screen."""

    def __init__(self, app):
        super().__init__(app.root)
        self.app = app
        st = app.settings
        self.custom_path = st["custom_path"]
        self.bg_path = st["background"]
        self.title("Settings")
        self.configure(bg=CARD)
        self.transient(app.root)
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = min(app.px(470), sw - 24), min(app.px(700), sh - 80)
        self.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 4)}")
        self.minsize(min(w, 280), min(h, 300))
        wrap = max(180, w - 70)

        sf = ScrollFrame(self)
        sf.pack(fill="both", expand=True)
        body = tk.Frame(sf.inner, bg=CARD)
        body.pack(fill="x", padx=18, pady=16)

        def label(text):
            tk.Label(body, text=text.upper(), bg=CARD, fg=MUTED,
                     font=("Helvetica", 8, "bold")).pack(anchor="w", pady=(14, 4))

        tk.Label(body, text="⚙ Settings", bg=CARD, fg="white",
                 font=("Helvetica", 15, "bold")).pack(anchor="w")

        # --- alarm sound list
        label("Alarm sound  (rings when the time arrives)")
        lf = tk.Frame(body, bg=CARD)
        lf.pack(fill="x")
        self.listbox = tk.Listbox(lf, height=7, exportselection=False, bg=INPUT, fg=TEXT,
                                  selectbackground=ACCENT, selectforeground="#ffffff",
                                  relief="flat", highlightthickness=1,
                                  highlightbackground=EDGE, activestyle="none",
                                  font=("Helvetica", 11))
        lsb = ttk.Scrollbar(lf, orient="vertical", command=self.listbox.yview)
        self.listbox.configure(yscrollcommand=lsb.set)
        self.listbox.pack(side="left", fill="x", expand=True)
        lsb.pack(side="right", fill="y")
        for n in ALL_SOUNDS:
            self.listbox.insert("end", n)
        idx = ALL_SOUNDS.index(st["alarm_sound"])
        self.listbox.selection_set(idx)
        self.listbox.see(idx)

        row = tk.Frame(body, bg=CARD)
        row.pack(fill="x", pady=(8, 0))
        HoverButton(row, "▶ Test", self.test_alarm, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "■ Stop", app.player.stop, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "📂 File…", self.choose_file, padx=10, pady=5).pack(side="left")
        self.custom_lbl = tk.Label(body, bg=CARD, fg=MUTED, font=("Helvetica", 9),
                                   anchor="w", justify="left", wraplength=wrap)
        self.custom_lbl.pack(fill="x", pady=(6, 0))
        self.update_custom_label()

        # --- reminder sound
        label("Reminder sound  (a little before the time)")
        row = tk.Frame(body, bg=CARD)
        row.pack(fill="x")
        self.rem_var = tk.StringVar(value=st["reminder_sound"])
        ttk.Combobox(row, textvariable=self.rem_var, state="readonly", width=18,
                     values=ALL_SOUNDS).pack(side="left")
        HoverButton(row, "▶", self.test_reminder, padx=10, pady=4).pack(side="left", padx=(8, 0))

        # --- volume
        label("Volume")
        row = tk.Frame(body, bg=CARD)
        row.pack(fill="x")
        self.vol = tk.IntVar(value=st["volume"])
        self.vol_lbl = tk.Label(row, text=f"{st['volume']}%", bg=CARD, fg="white", width=5,
                                font=("Helvetica", 11, "bold"))
        self.vol_lbl.pack(side="right")
        tk.Scale(row, from_=20, to=100, orient="horizontal", variable=self.vol, showvalue=False,
                 bg=CARD, fg=TEXT, troughcolor=INPUT, highlightthickness=0, bd=0,
                 activebackground=ACCENT, sliderrelief="flat",
                 command=lambda v: self.vol_lbl.configure(text=f"{int(float(v))}%")).pack(
            side="left", fill="x", expand=True)

        # --- ring length
        label("Ring for")
        current = next((t for t, s in RING_CHOICES if s == st["ring_seconds"]), "2 minutes")
        self.ring_var = tk.StringVar(value=current)
        ttk.Combobox(body, textvariable=self.ring_var, state="readonly", width=20,
                     values=[t for t, _ in RING_CHOICES]).pack(anchor="w")

        # --- snooze length
        label("Snooze length")
        self.snooze_var = tk.StringVar(value=self.snooze_text(st["snooze_min"]))
        ttk.Combobox(body, textvariable=self.snooze_var, state="readonly", width=20,
                     values=[self.snooze_text(n) for n in SNOOZE_CHOICES]).pack(anchor="w")

        # --- background
        label("Background")
        self.bg_lbl = tk.Label(body, bg=CARD, fg=MUTED, font=("Helvetica", 9),
                               anchor="w", justify="left", wraplength=wrap)
        self.bg_lbl.pack(fill="x")
        row = tk.Frame(body, bg=CARD)
        row.pack(fill="x", pady=(6, 0))
        HoverButton(row, "🎬 Choose…", self.choose_bg, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "↺ Default", self.reset_bg, padx=10, pady=5).pack(side="left")
        self.update_bg_label()
        self.bg_play = tk.BooleanVar(value=st["bg_play"])
        tk.Checkbutton(body, text="Play the animated background", variable=self.bg_play,
                       bg=CARD, fg=TEXT, selectcolor=INPUT, activebackground=CARD,
                       activeforeground=TEXT, highlightthickness=0, bd=0,
                       font=("Helvetica", 10)).pack(anchor="w", pady=(8, 4))
        cur_fps = next((t for t, f in FPS_CHOICES if f == st["bg_fps"]), FPS_CHOICES[1][0])
        self.fps_var = tk.StringVar(value=cur_fps)
        ttk.Combobox(body, textvariable=self.fps_var, state="readonly", width=22,
                     values=[t for t, _ in FPS_CHOICES]).pack(anchor="w")

        label("Scenery mode  (panels slide away when idle)")
        cur_idle = next((t for t, n in IDLE_CHOICES if n == st["idle_hide"]), "After 1 minute")
        self.idle_var = tk.StringVar(value=cur_idle)
        ttk.Combobox(body, textvariable=self.idle_var, state="readonly", width=22,
                     values=[t for t, _ in IDLE_CHOICES]).pack(anchor="w")

        tk.Label(body, text="Tip: your device's own volume still applies — turn it up for the "
                            "loudest alarm.", bg=CARD, fg=MUTED, font=("Helvetica", 9),
                 justify="left", anchor="w", wraplength=wrap).pack(fill="x", pady=(16, 0))

        btns = tk.Frame(body, bg=CARD)
        btns.pack(fill="x", pady=(16, 0))
        HoverButton(btns, "Save", self.save, bg=ACCENT, pady=9, pulse=True).pack(
            side="left", fill="x", expand=True)
        HoverButton(btns, "Close", self.close, pady=9).pack(side="left", padx=(8, 0))

        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self.focus_set()

    @staticmethod
    def snooze_text(n):
        return f"{n} minute" + ("" if n == 1 else "s")

    def update_custom_label(self):
        if self.custom_path and os.path.exists(self.custom_path):
            self.custom_lbl.configure(text=f"Custom file: {os.path.basename(self.custom_path)}")
        else:
            self.custom_lbl.configure(text="No custom file chosen (pick a .wav, then select “Custom file”).")

    def update_bg_label(self):
        if self.bg_path and os.path.exists(self.bg_path):
            self.bg_lbl.configure(text=f"Using: {os.path.basename(self.bg_path)}")
        else:
            self.bg_lbl.configure(text="Automatic: background.mp4 (or any video / space.jpg) "
                                       "from the app folder.")

    def selected_name(self):
        sel = self.listbox.curselection()
        return ALL_SOUNDS[sel[0]] if sel else self.app.settings["alarm_sound"]

    def test_alarm(self):
        self.app.preview(self.selected_name(), loop=True, seconds=6,
                         volume=int(self.vol.get()), custom=self.custom_path)

    def test_reminder(self):
        self.app.preview(self.rem_var.get(), loop=False, seconds=8,
                         volume=int(self.vol.get()), custom=self.custom_path)

    def choose_file(self):
        path = filedialog.askopenfilename(parent=self, title="Choose an alarm sound",
                                          filetypes=[("WAV audio", "*.wav")])
        if path:
            self.custom_path = path
            self.update_custom_label()
            idx = ALL_SOUNDS.index(CUSTOM)
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(idx)
            self.listbox.see(idx)

    def choose_bg(self):
        exts = " ".join("*" + e for e in VIDEO_EXT + IMAGE_EXT)
        path = filedialog.askopenfilename(parent=self, title="Choose a background",
                                          filetypes=[("Video or picture", exts), ("All files", "*.*")])
        if path:
            self.bg_path = path
            self.update_bg_label()

    def reset_bg(self):
        self.bg_path = ""
        self.update_bg_label()

    def save(self):
        name = self.selected_name()
        if name == CUSTOM and not (self.custom_path and os.path.exists(self.custom_path)):
            self.app.toast("Choose a .wav file first, or pick another sound")
            return
        st = self.app.settings
        bg_changed = st["background"] != self.bg_path
        st.update(alarm_sound=name, reminder_sound=self.rem_var.get(),
                  volume=int(self.vol.get()),
                  ring_seconds=dict(RING_CHOICES)[self.ring_var.get()],
                  snooze_min=int(self.snooze_var.get().split()[0]),
                  custom_path=self.custom_path, background=self.bg_path,
                  bg_play=bool(self.bg_play.get()),
                  bg_fps=dict(FPS_CHOICES)[self.fps_var.get()],
                  idle_hide=dict(IDLE_CHOICES)[self.idle_var.get()])
        self.app.save_settings()
        self.app.pregenerate()
        self.app.apply_background_settings(restart=bg_changed)
        self.app.toast("Settings saved ✓")
        self.close()

    def close(self):
        self.app.player.stop()
        self.destroy()


# ================================================================ main app
class ScheduleApp:
    FONTS = {   # header font sizes per layout mode
        "wide": dict(title=24, sub=11, clock=28, date=11, next=11),
        "compact": dict(title=16, sub=11, clock=17, date=9, next=10),
        "tiny": dict(title=14, sub=11, clock=15, date=9, next=9),
    }
    COLS_WIDE = ("date", "time", "title", "left", "status")
    COLS_MEDIUM = ("when", "title", "left")
    COLS_NARROW = ("when", "title")

    def __init__(self, root):
        self.root = root
        root.title("Schedule Planner")
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        w, h = min(1120, int(sw * 0.92)), min(720, int(sh * 0.88))
        root.geometry(f"{w}x{h}+{(sw - w) // 2}+{max(0, (sh - h) // 3)}")
        root.minsize(320, 460)
        root.configure(bg=BG)
        try:   # scale pixel sizes on high-DPI screens
            self.sc = max(1.0, min(2.5, root.winfo_fpixels("1i") / 96.0))
        except tk.TclError:
            self.sc = 1.0

        self.schedules = self.load()
        self.settings = self.load_settings()
        self.bank = SoundBank()
        self.player = SoundPlayer(root)
        self.editing_id = None
        self.filter = "All"
        self.status_cache = {}
        self.counts = dict.fromkeys(FILTERS, 0)
        self.popups = []
        self.toast_widget = None
        self.toast_job = None
        self.left_box = self.right_box = (0, 0, 0, 0)
        self.show_panels = True
        self.fullscreen = False
        self.mode = None
        self.compact = False
        self.tab = "list"
        self.W = self.H = 1
        self.top = self.px(96)
        self.chip_small = False
        self._cols = None
        # moving background + animation state
        self.engine = None
        self.bg_path = ""
        self.bg_photo = None
        self.bg_photo_size = None
        self.panel_shift = 0
        self.anim_job = None
        self.intro_wait = True
        self.stars_on = True
        self.win_base = {}
        self.lift_cur = {}
        self.lift_target = {}
        self.lift_job = None
        self.last_input = time.time()
        self.last_pos = (0, 0)
        self.idle_hidden = False
        self.idle_toast_shown = False

        self.setup_styles()
        self.canvas = tk.Canvas(root, bg=BG, highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.bg_item = self.canvas.create_image(0, 0, anchor="nw")
        self.card_rects = [self.canvas.create_rectangle(
            0, 0, 0, 0, fill=CARD, outline="#25376a") for _ in range(2)]   # used when no background

        self.make_stars()
        self.make_header()
        self.build_left()
        self.build_right()
        self.left_win = self.canvas.create_window(0, 0, window=self.left, anchor="nw")
        self.right_win = self.canvas.create_window(0, 0, window=self.right, anchor="nw")

        small = ("Helvetica", 9, "bold")
        lift = lambda name: (lambda up: self.lift_btn(getattr(self, name), up))
        self.nav_list = HoverButton(self.canvas, "📋 List", lambda: self.show_tab("list"),
                                    padx=8, pady=5, font=small, on_hover=lift("nav_list_win"))
        self.nav_new = HoverButton(self.canvas, "＋ New", lambda: self.show_tab("form"),
                                   padx=8, pady=5, font=small, on_hover=lift("nav_new_win"))
        self.scenery_btn = HoverButton(self.canvas, "🌌 View scenery", self.toggle_panels,
                                       padx=10, pady=5, font=small, on_hover=lift("scenery_win"))
        self.settings_btn = HoverButton(self.canvas, "⚙ Settings", self.open_settings,
                                        padx=10, pady=5, font=small, on_hover=lift("settings_win"))
        self.nav_list_win = self.canvas.create_window(0, 0, window=self.nav_list, anchor="nw")
        self.nav_new_win = self.canvas.create_window(0, 0, window=self.nav_new, anchor="nw")
        self.scenery_win = self.canvas.create_window(0, 0, window=self.scenery_btn, anchor="e")
        self.settings_win = self.canvas.create_window(0, 0, window=self.settings_btn, anchor="e")
        self.build_menu()

        notice = self.start_background()
        self.canvas.bind("<Configure>", self.on_resize)
        self.bind_keys()
        for seq in ("<Key>", "<ButtonPress>", "<MouseWheel>"):
            root.bind_all(seq, lambda e: self.wake_up(), add="+")
        root.bind_all("<Motion>", self.on_motion, add="+")
        root.bind("<Unmap>", self.on_unmap)
        root.bind("<Map>", self.on_map)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.reset_form()
        self.set_filter("All")
        self.pregenerate()
        self.tick()
        self.twinkle()
        self.pump_bg()
        root.after(450, self.start_intro)

        if notice:
            root.after(900, lambda: self.toast(notice))

    # ------------------------------------------------------------ helpers
    def px(self, n):
        return int(n * self.sc)

    def on_close(self):
        self.player.stop()
        self.stop_background()
        self.root.destroy()

    # ------------------------------------------------------------ storage
    def load(self):
        try:
            with open(SAVE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            return []
        for s in data:   # upgrade older save files
            s.setdefault("id", uuid.uuid4().hex)
            s.setdefault("snooze_until", "")
            s.setdefault("notes", "")
            s.setdefault("remind", 0)
            s.setdefault("reminded", False)
            s.setdefault("alerted", False)
            s.setdefault("done", False)
            s.setdefault("sound", "Default")
        return data

    def save(self):
        tmp = SAVE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.schedules, f, indent=2)
        os.replace(tmp, SAVE_FILE)

    def load_settings(self):
        st = dict(DEFAULT_SETTINGS)
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                st.update(json.load(f))
        except (FileNotFoundError, json.JSONDecodeError):
            pass
        if st["alarm_sound"] not in ALL_SOUNDS:
            st["alarm_sound"] = DEFAULT_SETTINGS["alarm_sound"]
        if st["reminder_sound"] not in ALL_SOUNDS:
            st["reminder_sound"] = DEFAULT_SETTINGS["reminder_sound"]
        for key, lo, hi in (("volume", 20, 100), ("ring_seconds", 0, 3600),
                            ("snooze_min", 1, 120), ("bg_fps", 5, 60),
                            ("idle_hide", 0, 3600)):
            try:   # each value is checked on its own, so one bad entry can't reset the rest
                st[key] = max(lo, min(hi, int(st[key])))
            except (TypeError, ValueError):
                st[key] = DEFAULT_SETTINGS[key]
        st["bg_play"] = bool(st["bg_play"])
        if not isinstance(st["background"], str):
            st["background"] = ""
        return st

    def save_settings(self):
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(self.settings, f, indent=2)

    @staticmethod
    def when(s):
        return datetime.strptime(s["when"], DT_FORMAT)

    def by_id(self, iid):
        return next((s for s in self.schedules if s["id"] == iid), None)

    def status_of(self, s, now=None):
        now = now or datetime.now()
        if s["done"]:
            return "Done"
        dt = self.when(s)
        if now >= dt:
            return "Overdue"
        if s["remind"] > 0 and now >= dt - timedelta(minutes=s["remind"]):
            return "Due soon"
        return "Upcoming"

    def countdown(self, s, now):
        if s["done"]:
            return "—"
        secs = (self.when(s) - now).total_seconds()
        if secs >= 0:
            return "in " + short_span(secs)
        return "overdue " + short_span(-secs)

    # ------------------------------------------------------------ moving background
    def start_background(self):
        """Pick a video (or picture), start decoding it. Returns a hint to show, or None."""
        self.stop_background()
        self.bg_photo = self.bg_photo_size = None
        notice = None
        if not HAS_PIL:
            self.set_stars_visible(True)
            return "Install Pillow for the background:  pip install pillow"
        pref = self.settings.get("background", "")
        video, image = find_media(BASE_DIR)
        for path in ([pref] if pref and os.path.exists(pref) else []) + [video, image]:
            if not path:
                continue
            ext = os.path.splitext(path)[1].lower()
            try:
                if ext in VIDEO_EXT:
                    if not HAS_CV2:
                        notice = "To play the video background:  pip install opencv-python"
                        continue
                    source = VideoSource(path)
                elif ext in IMAGE_EXT:
                    source = ImageSource(path)
                else:
                    continue
            except Exception:
                continue
            self.engine = BackgroundEngine(source, self.settings["bg_fps"])
            self.engine.set_paused(not self.settings["bg_play"])
            self.bg_path = path
            break
        if self.engine is None and notice is None:
            notice = "No background found — put background.mp4 next to this file"
        self.set_stars_visible(self.engine is None or self.engine.source.static)
        if self.W > 1:
            self.push_view()
            self.apply_visibility()
        return notice

    def stop_background(self):
        if self.engine is not None:
            self.engine.stop()
            self.engine = None

    def apply_background_settings(self, restart=False):
        if restart:
            notice = self.start_background()
            if notice:
                self.toast(notice)
        elif self.engine is not None:
            self.engine.set_fps(self.settings["bg_fps"])
            self.engine.set_paused(not self.settings["bg_play"])

    def pump_bg(self):
        """Copy the newest ready frame onto the canvas (cheap; decoding happens elsewhere)."""
        eng = self.engine
        if eng is not None:
            img = eng.take()
            if img is not None:
                if self.bg_photo is None or self.bg_photo_size != img.size:
                    self.bg_photo = ImageTk.PhotoImage(img)
                    self.bg_photo_size = img.size
                    self.canvas.itemconfigure(self.bg_item, image=self.bg_photo)
                else:
                    self.bg_photo.paste(img)
        self.root.after(10, self.pump_bg)

    def push_view(self):
        """Tell the background engine the window size and where the glass panels are."""
        if self.engine is None or self.W < 50:
            return
        sh = self.panel_shift
        boxes = []
        if self.panels_active():
            for box in ((self.left_box,) if self.compact else (self.left_box, self.right_box)):
                x0, y0, x1, y1 = box
                boxes.append((x0, y0 + sh, x1, y1 + sh))
        self.engine.set_view((self.W, self.H), boxes, self.top, self.px(40))

    def on_unmap(self, e):
        if e.widget is self.root and self.engine is not None:
            self.engine.set_paused(True)       # minimised: stop decoding to save battery

    def on_map(self, e):
        if e.widget is self.root and self.engine is not None:
            self.engine.set_paused(not self.settings["bg_play"])

    def set_stars_visible(self, on):
        self.stars_on = on
        for s in self.stars:
            self.canvas.itemconfigure(s["id"], state="normal" if on else "hidden")

    # ------------------------------------------------------------ sound plumbing
    def sound_path(self, name, volume=None, custom=None):
        volume = volume or self.settings["volume"]
        custom = self.settings["custom_path"] if custom is None else custom
        if name == SYSTEM:
            return None
        if name == CUSTOM:
            if custom and os.path.exists(custom):
                return custom
            name = "Classic Beeps"
        return self.bank.path(name, volume)

    def resolve_sound(self, name, kind="due"):
        if name in (None, "", "Default"):
            return self.settings["reminder_sound" if kind == "reminder" else "alarm_sound"]
        return name

    def preview(self, name, kind="due", loop=True, seconds=5, volume=None, custom=None):
        path = self.sound_path(self.resolve_sound(name, kind), volume, custom)
        self.player.play(path, loop=loop, seconds=seconds)

    def pregenerate(self):
        """Build the chosen sounds in the background so the alarm starts instantly."""
        names = {self.settings["alarm_sound"], self.settings["reminder_sound"]}

        def work():
            for n in names:
                if n in SOUND_NAMES:
                    self.bank.path(n, self.settings["volume"])

        threading.Thread(target=work, daemon=True).start()

    def start_sound(self, s, kind):
        """Called by a new popup. Returns the ring length in seconds (None = until stopped)."""
        if kind == "reminder":
            if any(p.alive and p.loud for p in self.popups):
                return None   # don't interrupt a ringing alarm
            path = self.sound_path(self.settings["reminder_sound"])
            self.player.play(path, loop=False, seconds=8)
            return None
        name = self.resolve_sound(s.get("sound"), "due")
        secs = self.settings["ring_seconds"] or None
        self.player.play(self.sound_path(name), loop=True, seconds=secs)
        return secs

    def popup_closed(self):
        if not any(p.alive and p.loud for p in self.popups):
            self.player.stop()

    def open_settings(self):
        SettingsDialog(self)

    def preview_form_sound(self):
        self.preview(self.sound_var.get(), loop=True, seconds=4)

    # ------------------------------------------------------------ styling
    def setup_styles(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("Treeview", background=TABLE_BG, fieldbackground=TABLE_BG,
                     foreground=TEXT, rowheight=self.px(32), borderwidth=0,
                     font=("Helvetica", 10))
        st.map("Treeview", background=[("selected", ACCENT)],
               foreground=[("selected", "#ffffff")])
        st.configure("Treeview.Heading", background="#16213d", foreground=TEXT,
                     relief="flat", font=("Helvetica", 9, "bold"), padding=6)
        st.map("Treeview.Heading", background=[("active", "#22325a")])
        st.configure("Vertical.TScrollbar", background=BTN, troughcolor=TABLE_BG,
                     bordercolor=TABLE_BG, arrowcolor=TEXT, relief="flat")
        st.configure("TCombobox", fieldbackground=INPUT, background=BTN,
                     foreground=TEXT, arrowcolor=TEXT, bordercolor=EDGE,
                     lightcolor=INPUT, darkcolor=INPUT, selectbackground=INPUT,
                     selectforeground=TEXT, padding=4)
        st.map("TCombobox", fieldbackground=[("readonly", INPUT)],
               foreground=[("readonly", TEXT)],
               selectbackground=[("readonly", INPUT)],
               selectforeground=[("readonly", TEXT)])
        self.root.option_add("*TCombobox*Listbox.background", INPUT)
        self.root.option_add("*TCombobox*Listbox.foreground", TEXT)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")

    # ------------------------------------------------------------ header + stars
    def make_header(self):
        c = self.canvas

        def pair(text, font, anchor, fill):
            shadow = c.create_text(0, 0, text=text, font=font, anchor=anchor, fill="#000000")
            main = c.create_text(0, 0, text=text, font=font, anchor=anchor, fill=fill)
            return shadow, main

        self.title_items = pair("✦ PlanIt", ("Helvetica", 24, "bold"), "w", "#ffffff")
        self.sub_items = pair("Plan it. Make it. Never miss a moment.",
                              ("Helvetica", 11), "w", "#cfe0ff")
        self.clock_items = pair("", ("Helvetica", 28, "bold"), "e", "#ffffff")
        self.date_items = pair("", ("Helvetica", 11), "e", "#cfe0ff")
        self.next_items = pair("", ("Helvetica", 11, "bold"), "w", GOLD)

    def apply_mode_style(self):
        """Header fonts / visibility for the current layout mode."""
        f, c, mode = self.FONTS[self.mode], self.canvas, self.mode

        def style(items, size, bold, hidden=False):
            font = ("Helvetica", size, "bold") if bold else ("Helvetica", size)
            for i in items:
                c.itemconfigure(i, font=font, state="hidden" if hidden else "normal")

        self.set_pair(self.title_items, "✦ Planner" if mode == "tiny" else "✦ PlanIt")
        style(self.title_items, f["title"], True)
        style(self.sub_items, f["sub"], False, hidden=(mode != "wide"))
        style(self.clock_items, f["clock"], True)
        style(self.date_items, f["date"], False, hidden=(mode == "tiny"))
        style(self.next_items, f["next"], True)

    def put_pair(self, items, x, y):
        self.canvas.coords(items[0], x + 1, y + 1)
        self.canvas.coords(items[1], x, y)

    def set_pair(self, items, text):
        for i in items:
            self.canvas.itemconfigure(i, text=text)

    def make_stars(self):
        rnd = random.Random(7)
        self.stars = []
        for i in range(70):
            item = self.canvas.create_oval(0, 0, 0, 0, fill="#566aa8", outline="")
            self.stars.append({"fx": rnd.random(), "fy": rnd.random(), "id": item,
                               "r": rnd.choice([1, 1, 1, 2]), "top": i % 2 == 0})

    def place_stars(self, W, H):
        for s in self.stars:
            x = s["fx"] * W
            y = s["fy"] * (max(10, self.top - 6) if s["top"] else H)
            r = s["r"]
            self.canvas.coords(s["id"], x - r, y - r, x + r, y + r)

    def twinkle(self):
        if self.stars_on:
            palette = ["#2b3a6a", "#566aa8", "#aac4ff", "#ffffff"]
            for s in random.sample(self.stars, 8):
                self.canvas.itemconfigure(s["id"], fill=random.choice(palette))
        self.root.after(120, self.twinkle)

    # ------------------------------------------------------------ button lift (header)
    def put_win(self, win, x, y):
        """Place a canvas window, remembering its resting position for the lift effect."""
        self.win_base[win] = (x, y)
        self.canvas.coords(win, x, y + self.lift_cur.get(win, 0))

    def lift_btn(self, win, up):
        self.lift_target[win] = -3 if up else 0
        if self.lift_job is None:
            self.lift_job = self.root.after(16, self.lift_step)

    def lift_step(self):
        busy = False
        for win, target in self.lift_target.items():
            cur = self.lift_cur.get(win, 0.0)
            new = cur + (target - cur) * 0.4
            if abs(target - new) < 0.2:
                new = float(target)
            else:
                busy = True
            if new != cur and win in self.win_base:
                self.lift_cur[win] = new
                bx, by = self.win_base[win]
                self.canvas.coords(win, bx, by + new)
        self.lift_job = self.root.after(16, self.lift_step) if busy else None

    # ------------------------------------------------------------ responsive layout
    def on_resize(self, e):
        self.layout(e.width, e.height)

    def scenery_text(self, short):
        if self.show_panels:
            return "🌌 Scenery" if short else "🌌 View scenery"
        return "📋 Planner" if short else "📋 Back to planner"

    def hide_distance(self):
        return max(self.H - self.top, 120) + self.px(30)

    def panels_active(self):
        return self.show_panels or self.panel_shift < self.hide_distance() - 1

    def layout(self, W, H):
        px, c = self.px, self.canvas
        self.W, self.H = W, H
        lo = compute_layout(W, H, self.sc)
        if lo["mode"] != self.mode:
            self.mode = lo["mode"]
            self.apply_mode_style()
        self.compact = lo["compact"]
        m, p = lo["m"], px(5)
        self.top = lo["top"]
        self.left_box, self.right_box = lo["left"], lo["right"]

        for win, box in ((self.left_win, self.left_box), (self.right_win, self.right_box)):
            x0, y0, x1, y1 = box
            c.itemconfigure(win, width=max(10, x1 - x0 - 2 * p), height=max(10, y1 - y0 - 2 * p))

        # --- header texts + buttons
        if self.compact:
            self.put_pair(self.title_items, m + 2, px(24))
            self.put_pair(self.clock_items, W - m, px(24))
            self.put_pair(self.date_items, W - m, px(46))
            n, gap = 4, px(6)
            bw = (W - 2 * m - (n - 1) * gap) // n
            icons = bw < px(92)
            labels = [("📋 List", "📋"), ("＋ New", "＋"),
                      (self.scenery_text(True), self.scenery_text(True).split()[0]),
                      ("⚙ Settings", "⚙")]
            wins = (self.nav_list_win, self.nav_new_win, self.scenery_win, self.settings_win)
            btns = (self.nav_list, self.nav_new, self.scenery_btn, self.settings_btn)
            for i, (win, btn, (full, icon)) in enumerate(zip(wins, btns, labels)):
                btn.configure(text=icon if icons else full)
                c.itemconfigure(win, anchor="nw", width=bw, height=px(34), state="normal")
                self.put_win(win, m + i * (bw + gap), px(68))
        else:
            self.put_pair(self.title_items, m + 4, px(38))
            self.put_pair(self.sub_items, m + 6, px(68))
            self.put_pair(self.clock_items, W - m, px(38))
            self.put_pair(self.date_items, W - m, px(70))
            for win in (self.nav_list_win, self.nav_new_win):
                c.itemconfigure(win, state="hidden")
            self.scenery_btn.configure(text=self.scenery_text(False))
            self.settings_btn.configure(text="⚙ Settings")
            est = lambda t: int(len(t) * 7.4 * self.sc) + px(30)
            x = W - m - px(190)
            c.itemconfigure(self.scenery_win, anchor="e", width="", height="", state="normal")
            self.put_win(self.scenery_win, x, px(52))
            c.itemconfigure(self.settings_win, anchor="e", width="", height="", state="normal")
            self.put_win(self.settings_win, x - est(self.scenery_text(False)) - px(8), px(52))
        self.put_pair(self.next_items, m + 2, H - px(20))
        self.place_stars(W, H)

        # keep the panels where they belong (unless an animation is moving them)
        if self.intro_wait:
            self.panel_shift = self.hide_distance()
        elif self.anim_job is None:
            self.panel_shift = 0 if self.show_panels else self.hide_distance()
        self.apply_visibility()
        self.place_panels()
        cardw = self.right_box[2] - self.right_box[0]
        self.adapt_right(cardw)
        self.detail.configure(wraplength=max(160, cardw - px(60)))

    def place_panels(self):
        """Position the cards (including their slide offset) and the glass behind them."""
        c, p, sh = self.canvas, self.px(5), self.panel_shift
        for win, box in ((self.left_win, self.left_box), (self.right_win, self.right_box)):
            c.coords(win, box[0] + p, box[1] + p + sh)
        for rect, box in zip(self.card_rects, (self.left_box, self.right_box)):
            c.coords(rect, box[0], box[1] + sh, box[2], box[3] + sh)
        self.push_view()

    def apply_visibility(self):
        c = self.canvas
        active = self.panels_active()
        show_left = active and (not self.compact or self.tab == "form")
        show_right = active and (not self.compact or self.tab == "list")
        for win, show in ((self.left_win, show_left), (self.right_win, show_right)):
            c.itemconfigure(win, state="normal" if show else "hidden")
        no_bg = self.engine is None
        for rect, show in zip(self.card_rects, (show_left, show_right)):
            c.itemconfigure(rect, state="normal" if (show and no_bg) else "hidden")
        self.nav_list.set_base(ACCENT if self.tab == "list" else BTN)
        self.nav_new.set_base(ACCENT if self.tab == "form" else BTN)
        for win in (self.nav_list_win, self.nav_new_win):
            c.itemconfigure(win, state="normal" if self.compact else "hidden")

    def adapt_right(self, cardw):
        """Show fewer table columns / smaller chips when the list panel is narrow."""
        px = self.px
        cols = (self.COLS_WIDE if cardw >= px(600) else
                self.COLS_MEDIUM if cardw >= px(420) else self.COLS_NARROW)
        if cols != self._cols:
            self._cols = cols
            self.tree.configure(displaycolumns=cols)
        small = cardw < px(440)
        if small != self.chip_small:
            self.chip_small = small
            self.update_chips()
            for b in self.action_btns:
                b.configure(padx=px(8) if small else px(14))
        if self.compact and self.hint.winfo_manager():
            self.hint.pack_forget()
        elif not self.compact and not self.hint.winfo_manager():
            self.hint.pack(side="bottom", anchor="w", pady=(8, 0), before=self.actions)

    def show_tab(self, tab):
        self.tab = tab
        self.apply_visibility()

    # ------------------------------------------------------------ panel animation
    def start_intro(self):
        self.intro_wait = False
        self.animate_panels(0)

    def animate_panels(self, target, steps=22):
        """Glide the cards to `target` px of vertical offset (0 = in place)."""
        if self.anim_job is not None:
            self.root.after_cancel(self.anim_job)
        start = self.panel_shift
        showing = target < start

        def step(i=1):
            k = i / steps
            if showing:   # ease-out-back: slides in, overshoots a hair, settles
                c1 = 1.25
                ease = 1 + (c1 + 1) * (k - 1) ** 3 + c1 * (k - 1) ** 2
            else:         # ease-in-out cubic: gathers speed, then drops away
                ease = 4 * k ** 3 if k < 0.5 else 1 - (-2 * k + 2) ** 3 / 2
            self.panel_shift = int(start + (target - start) * ease)
            self.place_panels()
            if i < steps:
                self.anim_job = self.root.after(16, step, i + 1)
            else:
                self.anim_job = None
                self.panel_shift = target
                self.apply_visibility()
                self.place_panels()

        step()

    def set_panels(self, show):
        """Slide the panels away (or back) so the whole video can be enjoyed."""
        if show == self.show_panels:
            return
        start = self.panel_shift          # layout() snaps panels to their end state, so
        self.show_panels = show           # remember where they are and animate from there
        self.apply_visibility()
        self.layout(self.W, self.H)
        self.panel_shift = start
        self.place_panels()
        self.animate_panels(0 if show else self.hide_distance())

    def toggle_panels(self):
        self.idle_hidden = False
        self.set_panels(not self.show_panels)

    # ---- idle "scenery mode"
    def on_motion(self, e):
        pos = (e.x_root, e.y_root)
        if abs(pos[0] - self.last_pos[0]) + abs(pos[1] - self.last_pos[1]) >= 3:   # real movement only
            self.last_pos = pos
            self.wake_up()

    def wake_up(self):
        self.last_input = time.time()
        if self.idle_hidden:
            self.idle_hidden = False
            self.set_panels(True)

    def check_idle(self):
        secs = self.settings["idle_hide"]
        if (not secs or not self.show_panels or self.engine is None or self.popups
                or self.anim_job is not None or self.editing_id or self.title_var.get().strip()
                or any(isinstance(w, tk.Toplevel) for w in self.root.winfo_children())
                or time.time() - self.last_input < secs):
            return
        self.idle_hidden = True
        self.set_panels(False)
        if not self.idle_toast_shown:
            self.idle_toast_shown = True
            self.toast("Scenery mode — move the mouse to bring the planner back")

    def toggle_fullscreen(self):
        self.fullscreen = not self.fullscreen
        self.root.attributes("-fullscreen", self.fullscreen)

    # ------------------------------------------------------------ small ui helpers
    def entry(self, parent, var, width=10):
        return tk.Entry(parent, textvariable=var, width=width, bg=INPUT, fg=TEXT,
                        insertbackground=TEXT, relief="flat", font=("Helvetica", 11),
                        highlightthickness=1, highlightbackground=EDGE,
                        highlightcolor=ACCENT)

    def spin(self, parent, var, maxv):
        return tk.Spinbox(parent, from_=0, to=maxv, width=3, wrap=True, format="%02.0f",
                          textvariable=var, bg=INPUT, fg=TEXT, buttonbackground=BTN,
                          insertbackground=TEXT, relief="flat", font=("Helvetica", 12),
                          highlightthickness=1, highlightbackground=EDGE,
                          highlightcolor=ACCENT, justify="center")

    def field_label(self, parent, text):
        tk.Label(parent, text=text.upper(), bg=CARD, fg=MUTED,
                 font=("Helvetica", 8, "bold")).pack(anchor="w", pady=(10, 3))

    def flash(self, widget):
        widget.configure(highlightbackground=DANGER, highlightcolor=DANGER)
        self.root.after(900, lambda: widget.winfo_exists() and widget.configure(
            highlightbackground=EDGE, highlightcolor=ACCENT))

    # ------------------------------------------------------------ left card (form, scrollable)
    def build_left(self):
        self.left = tk.Frame(self.canvas, bg=CARD)
        scroller = ScrollFrame(self.left)
        scroller.pack(fill="both", expand=True)
        inner = tk.Frame(scroller.inner, bg=CARD)
        inner.pack(fill="x", padx=16, pady=14)

        self.title_var = tk.StringVar()
        self.date_var = tk.StringVar()
        self.hour_var = tk.StringVar()
        self.min_var = tk.StringVar()
        self.remind_var = tk.StringVar()
        self.sound_var = tk.StringVar(value="Default")

        self.form_title = tk.Label(inner, text="＋ New schedule", bg=CARD, fg="#ffffff",
                                   font=("Helvetica", 14, "bold"))
        self.form_title.pack(anchor="w")

        self.field_label(inner, "Title")
        self.title_entry = self.entry(inner, self.title_var)
        self.title_entry.pack(fill="x", ipady=5)

        self.field_label(inner, "Date  (YYYY-MM-DD)")
        row = tk.Frame(inner, bg=CARD)
        row.pack(fill="x")
        self.date_entry = self.entry(row, self.date_var, width=12)
        self.date_entry.pack(side="left", ipady=5)
        HoverButton(row, "📅", self.open_calendar, padx=9, pady=4).pack(side="left", padx=(6, 0))
        HoverButton(row, "Today", self.set_today, padx=10, pady=4,
                    font=("Helvetica", 9, "bold")).pack(side="left", padx=(6, 0))

        self.field_label(inner, "Time  (24-hour)")
        row = tk.Frame(inner, bg=CARD)
        row.pack(fill="x")
        self.hour_spin = self.spin(row, self.hour_var, 23)
        self.hour_spin.pack(side="left", ipady=4)
        tk.Label(row, text=":", bg=CARD, fg=TEXT, font=("Helvetica", 14, "bold")).pack(side="left", padx=3)
        self.min_spin = self.spin(row, self.min_var, 59)
        self.min_spin.pack(side="left", ipady=4)

        chips = tk.Frame(inner, bg=CARD)
        chips.pack(fill="x", pady=(8, 0))
        small = ("Helvetica", 8, "bold")
        HoverButton(chips, "+30 min", lambda: self.quick(timedelta(minutes=30)),
                    padx=8, pady=3, font=small).pack(side="left", padx=(0, 5))
        HoverButton(chips, "+1 hour", lambda: self.quick(timedelta(hours=1)),
                    padx=8, pady=3, font=small).pack(side="left", padx=(0, 5))
        HoverButton(chips, "Tomorrow 9:00", lambda: self.quick(None),
                    padx=8, pady=3, font=small).pack(side="left")

        self.field_label(inner, "Remind me before")
        row = tk.Frame(inner, bg=CARD)
        row.pack(fill="x")
        ttk.Combobox(row, textvariable=self.remind_var, width=6,
                     values=["0", "5", "10", "15", "30", "60", "120", "1440"]).pack(side="left")
        tk.Label(row, text="minutes  (0 = none)", bg=CARD, fg=MUTED,
                 font=("Helvetica", 9)).pack(side="left", padx=8)

        self.field_label(inner, "Alarm sound")
        row = tk.Frame(inner, bg=CARD)
        row.pack(fill="x")
        ttk.Combobox(row, textvariable=self.sound_var, state="readonly", width=17,
                     values=["Default"] + ALL_SOUNDS).pack(side="left")
        HoverButton(row, "▶", self.preview_form_sound, padx=9, pady=4).pack(side="left", padx=(6, 0))
        HoverButton(row, "■", self.player.stop, padx=9, pady=4).pack(side="left", padx=(4, 0))

        self.field_label(inner, "Notes")
        self.notes_text = tk.Text(inner, height=3, wrap="word", bg=INPUT, fg=TEXT,
                                  insertbackground=TEXT, relief="flat", padx=8, pady=6,
                                  font=("Helvetica", 10), highlightthickness=1,
                                  highlightbackground=EDGE, highlightcolor=ACCENT)
        self.notes_text.pack(fill="x")

        btns = tk.Frame(inner, bg=CARD)
        btns.pack(fill="x", pady=(16, 0))
        self.save_btn = HoverButton(btns, "Add schedule", self.save_schedule, bg=ACCENT,
                                    pady=9, pulse=True)   # the glow "breathes" to invite a click
        self.save_btn.pack(side="left", fill="x", expand=True)
        HoverButton(btns, "Clear", self.reset_form, pady=9).pack(side="left", padx=(8, 0))

    # ------------------------------------------------------------ right card (table)
    def build_right(self):
        self.right = tk.Frame(self.canvas, bg=CARD)
        inner = tk.Frame(self.right, bg=CARD)
        inner.pack(fill="both", expand=True, padx=14, pady=12)

        top = tk.Frame(inner, bg=CARD)
        top.pack(fill="x")
        self.chips = {}
        for name in FILTERS:
            b = HoverButton(top, name, lambda n=name: self.set_filter(n), padx=11, pady=5,
                            font=("Helvetica", 9, "bold"))
            b.pack(side="left", padx=(0, 5))
            self.chips[name] = b

        wrap = tk.Frame(inner, bg=INPUT, highlightthickness=1,
                        highlightbackground=EDGE, highlightcolor=ACCENT)
        wrap.pack(fill="x", pady=(10, 0))
        tk.Label(wrap, text="🔍", bg=INPUT, fg=MUTED).pack(side="left", padx=(8, 0))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self.refresh_table())
        self.search_entry = tk.Entry(wrap, textvariable=self.search_var, bg=INPUT, fg=TEXT,
                                     insertbackground=TEXT, relief="flat",
                                     font=("Helvetica", 10), highlightthickness=0)
        self.search_entry.pack(side="left", fill="x", expand=True, ipady=5, padx=6)
        self.search_entry.bind("<FocusIn>", lambda e: wrap.configure(highlightbackground=ACCENT))
        self.search_entry.bind("<FocusOut>", lambda e: wrap.configure(highlightbackground=EDGE))

        # pack the bottom rows first so the table can never push them out of view
        self.hint = tk.Label(inner, text="Double-click to edit  ·  Right-click for options  ·  Del to delete",
                             bg=CARD, fg=FAINT, font=("Helvetica", 8))
        self.hint.pack(side="bottom", anchor="w", pady=(8, 0))
        actions = self.actions = tk.Frame(inner, bg=CARD)
        actions.pack(side="bottom", fill="x", pady=(8, 0))
        self.action_btns = [
            HoverButton(actions, "Edit", self.edit_selected),
            HoverButton(actions, "Done / Undo", self.toggle_done),
            HoverButton(actions, "Duplicate", self.duplicate_selected),
            HoverButton(actions, "Delete", self.delete_selected, bg=DANGER),
        ]
        for b in self.action_btns:
            b.pack(side="left", padx=(0, 5))
        self.detail = tk.Label(inner, text="", bg=CARD, fg=MUTED, justify="left", anchor="nw",
                               height=3, font=("Helvetica", 10), wraplength=520)
        self.detail.pack(side="bottom", fill="x")

        table = tk.Frame(inner, bg=CARD)
        table.pack(fill="both", expand=True, pady=10)
        cols = ("date", "time", "when", "title", "left", "status")
        self.tree = ttk.Treeview(table, columns=cols, show="headings", selectmode="browse",
                                 displaycolumns=self.COLS_WIDE)
        for col, text, width, stretch in [("date", "Date", 100, False), ("time", "Time", 56, False),
                                          ("when", "When", 118, False),
                                          ("title", "Title", 150, True),
                                          ("left", "Countdown", 112, False),
                                          ("status", "Status", 84, False)]:
            self.tree.heading(col, text=text, anchor="w")
            self.tree.column(col, width=width, minwidth=40, anchor="w", stretch=stretch)
        sb = ttk.Scrollbar(table, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.tag_configure("overdue", background="#2a1220", foreground="#ff8aa0")
        self.tree.tag_configure("soon", background="#2a2410", foreground=GOLD)
        self.tree.tag_configure("done", foreground=FAINT)
        self.empty = tk.Label(self.tree, text="Nothing here yet ✨", bg=TABLE_BG, fg=MUTED,
                              font=("Helvetica", 12))

    def build_menu(self):
        self.menu = tk.Menu(self.root, tearoff=0, bg=CARD, fg=TEXT, bd=0,
                            activebackground=ACCENT, activeforeground="#ffffff",
                            font=("Helvetica", 10))

    def bind_keys(self):
        r = self.root
        r.bind("<Delete>", lambda e: self.key_action(self.delete_selected))
        r.bind("<Control-n>", lambda e: (self.reset_form(), self.show_tab("form"),
                                         self.title_entry.focus_set()))
        r.bind("<Control-f>", lambda e: (self.show_tab("list"), self.search_entry.focus_set()))
        r.bind("<F11>", lambda e: self.toggle_fullscreen())
        r.bind("<Escape>", self.on_escape)
        for w in (self.title_entry, self.date_entry):
            w.bind("<Return>", lambda e: self.save_schedule())
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.show_details())
        self.tree.bind("<Double-1>", self.on_double)
        for seq in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
            self.tree.bind(seq, self.on_right_click)

    def on_escape(self, _e):
        if self.fullscreen:
            self.toggle_fullscreen()
        elif self.editing_id:
            self.reset_form()

    def key_action(self, fn):
        try:
            focus = self.root.focus_get()
        except KeyError:
            focus = None
        if isinstance(focus, (tk.Entry, tk.Text, tk.Spinbox, ttk.Combobox)):
            return
        fn()

    # ------------------------------------------------------------ form actions
    def set_today(self):
        self.date_var.set(date.today().strftime("%Y-%m-%d"))

    def quick(self, delta):
        dt = (datetime.now() + delta) if delta else datetime.combine(
            date.today() + timedelta(days=1), dtime(9, 0))
        self.date_var.set(dt.strftime("%Y-%m-%d"))
        self.hour_var.set(dt.strftime("%H"))
        self.min_var.set(dt.strftime("%M"))

    def open_calendar(self):
        try:
            initial = datetime.strptime(self.date_var.get().strip(), "%Y-%m-%d").date()
        except ValueError:
            initial = date.today()
        DatePicker(self, initial, self.date_var.set)

    def reset_form(self):
        self.editing_id = None
        self.form_title.configure(text="＋ New schedule")
        self.save_btn.configure(text="Add schedule")
        later = datetime.now() + timedelta(minutes=15)
        self.title_var.set("")
        self.date_var.set(later.strftime("%Y-%m-%d"))
        self.hour_var.set(later.strftime("%H"))
        self.min_var.set(later.strftime("%M"))
        self.remind_var.set("10")
        self.sound_var.set("Default")
        self.notes_text.delete("1.0", tk.END)

    def save_schedule(self):
        title = self.title_var.get().strip()
        if not title:
            self.flash(self.title_entry)
            self.toast("Please enter a title")
            self.title_entry.focus_set()
            return
        try:
            d = datetime.strptime(self.date_var.get().strip(), "%Y-%m-%d")
        except ValueError:
            self.flash(self.date_entry)
            self.toast("Date should look like 2026-10-25 — or use the 📅 picker")
            return
        try:
            h, mi = int(self.hour_var.get()), int(self.min_var.get())
            if not (0 <= h <= 23 and 0 <= mi <= 59):
                raise ValueError
        except ValueError:
            self.flash(self.hour_spin)
            self.flash(self.min_spin)
            self.toast("Time must be 00:00 – 23:59")
            return
        try:
            remind = max(0, int(self.remind_var.get()))
        except ValueError:
            self.toast("Reminder must be a whole number of minutes")
            return

        when = d.replace(hour=h, minute=mi)
        when_s = when.strftime(DT_FORMAT)
        now = datetime.now()
        existing = self.by_id(self.editing_id) if self.editing_id else None
        time_changed = (existing is None or existing["when"] != when_s
                        or existing["remind"] != remind)
        if when < now.replace(second=0, microsecond=0) and time_changed:
            self.flash(self.date_entry)
            self.toast("That time has already passed — pick a future time")
            return

        notes = self.notes_text.get("1.0", tk.END).strip()
        sound = self.sound_var.get() or "Default"
        remind_passed = remind == 0 or now >= when - timedelta(minutes=remind)
        if existing:
            existing.update(title=title, notes=notes, when=when_s, remind=remind, sound=sound)
            if time_changed:   # re-arm the alarms for the new time
                existing.update(reminded=remind_passed, alerted=False,
                                snooze_until="", done=False)
            target, msg = existing["id"], "Schedule updated ✓"
        else:
            target = uuid.uuid4().hex
            self.schedules.append({
                "id": target, "title": title, "when": when_s, "remind": remind,
                "notes": notes, "done": False, "reminded": remind_passed,
                "alerted": False, "snooze_until": "", "sound": sound,
            })
            msg = "Schedule added ✓"

        self.save()
        self.reset_form()
        self.refresh_table()
        if self.compact:
            self.show_tab("list")
        if self.tree.exists(target):
            self.tree.selection_set(target)
            self.tree.see(target)
        self.toast(msg)

    # ------------------------------------------------------------ table actions
    def selected(self, quiet=False):
        sel = self.tree.selection()
        s = self.by_id(sel[0]) if sel else None
        if s is None and not quiet:
            self.toast("Select a schedule first")
        return s

    def edit_selected(self):
        s = self.selected()
        if not s:
            return
        dt = self.when(s)
        self.editing_id = s["id"]
        self.form_title.configure(text="✎ Edit schedule")
        self.save_btn.configure(text="Update schedule")
        self.title_var.set(s["title"])
        self.date_var.set(dt.strftime("%Y-%m-%d"))
        self.hour_var.set(dt.strftime("%H"))
        self.min_var.set(dt.strftime("%M"))
        self.remind_var.set(str(s["remind"]))
        self.sound_var.set(s.get("sound", "Default"))
        self.notes_text.delete("1.0", tk.END)
        self.notes_text.insert("1.0", s["notes"])
        if self.compact:
            self.show_tab("form")
        self.title_entry.focus_set()

    def toggle_done(self):
        s = self.selected()
        if not s:
            return
        now = datetime.now()
        s["done"] = not s["done"]
        if not s["done"]:   # un-done: don't ring for things already in the past
            s["alerted"] = now >= self.when(s)
            s["reminded"] = s["remind"] == 0 or now >= self.when(s) - timedelta(minutes=s["remind"])
            s["snooze_until"] = ""
        self.save()
        self.refresh_table()
        self.toast("Marked as done ✓" if s["done"] else "Moved back to active")

    def duplicate_selected(self):
        s = self.selected()
        if not s:
            return
        copy = dict(s, id=uuid.uuid4().hex, done=False, alerted=False, snooze_until="",
                    when=(self.when(s) + timedelta(days=1)).strftime(DT_FORMAT))
        copy["reminded"] = copy["remind"] == 0
        self.schedules.append(copy)
        self.save()
        self.refresh_table()
        self.tree.selection_set(copy["id"])
        self.tree.see(copy["id"])
        self.toast("Duplicated to the next day")

    def delete_selected(self):
        s = self.selected()
        if not s:
            return
        idx = self.schedules.index(s)
        self.schedules.remove(s)
        self.save()
        self.refresh_table()

        def undo():
            self.schedules.insert(min(idx, len(self.schedules)), s)
            self.save()
            self.refresh_table()

        self.toast(f"Deleted “{s['title'][:28]}”", action=("Undo", undo))

    def on_double(self, e):
        if self.tree.identify_region(e.x, e.y) == "cell":
            self.edit_selected()

    def on_right_click(self, e):
        iid = self.tree.identify_row(e.y)
        if not iid:
            return
        self.tree.selection_set(iid)
        s = self.by_id(iid)
        self.menu.delete(0, "end")
        self.menu.add_command(label="Edit", command=self.edit_selected)
        self.menu.add_command(label="Mark as not done" if s["done"] else "Mark as done",
                              command=self.toggle_done)
        self.menu.add_command(label="Duplicate to next day", command=self.duplicate_selected)
        self.menu.add_separator()
        self.menu.add_command(label="Delete", command=self.delete_selected)
        try:
            self.menu.tk_popup(e.x_root, e.y_root)
        finally:
            self.menu.grab_release()

    def set_filter(self, name):
        self.filter = name
        for n, b in self.chips.items():
            b.set_base(ACCENT if n == name else BTN)
        self.refresh_table()

    def matches(self, name, status, dt, now):
        return {"All": True,
                "Today": dt.date() == now.date(),
                "Upcoming": status in ("Upcoming", "Due soon"),
                "Overdue": status == "Overdue",
                "Done": status == "Done"}[name]

    def update_chips(self):
        small = self.chip_small
        for name, b in self.chips.items():
            n = self.counts[name]
            b.configure(text=name if (small or not n) else f"{name}  {n}",
                        padx=self.px(5) if small else self.px(11),
                        font=("Helvetica", 8 if small else 9, "bold"))

    def refresh_table(self):
        """Full rebuild - only runs when something actually changed (no flicker)."""
        now = datetime.now()
        keep = self.tree.selection()
        self.tree.delete(*self.tree.get_children())
        query = self.search_var.get().strip().lower()
        statuses, counts = {}, dict.fromkeys(FILTERS, 0)

        for s in sorted(self.schedules, key=lambda x: (x["done"], x["when"])):
            st = self.status_of(s, now)
            dt = self.when(s)
            statuses[s["id"]] = st
            for name in FILTERS:
                if self.matches(name, st, dt, now):
                    counts[name] += 1
            if not self.matches(self.filter, st, dt, now):
                continue
            if query and query not in s["title"].lower() and query not in s["notes"].lower():
                continue
            tag = {"Overdue": "overdue", "Due soon": "soon", "Done": "done"}.get(st, "")
            self.tree.insert("", "end", iid=s["id"], tags=(tag,), values=(
                dt.strftime("%b %d, %Y"), dt.strftime("%H:%M"), dt.strftime("%b %d · %H:%M"),
                s["title"], self.countdown(s, now), st))

        self.status_cache = statuses
        self.counts = counts
        self.update_chips()
        if self.tree.get_children():
            self.empty.place_forget()
        else:
            self.empty.place(relx=0.5, rely=0.5, anchor="center")
        for iid in keep:
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
        self.show_details()

    def show_details(self):
        s = self.selected(quiet=True)
        if not s:
            self.detail.configure(text="Select a schedule to see its details.")
            return
        dt = self.when(s)
        remind = f"reminder {s['remind']} min before" if s["remind"] else "no reminder"
        sound = self.resolve_sound(s.get("sound"), "due")
        notes = s["notes"].replace("\n", " ")
        notes = (notes[:150] + "…") if len(notes) > 150 else (notes or "No notes")
        self.detail.configure(
            text=f"{s['title']}\n{dt:%A, %B %d, %Y at %H:%M}  ·  {remind}  ·  🔊 {sound}\n{notes}")

    # ------------------------------------------------------------ toast
    def toast(self, text, action=None):
        self.hide_toast()
        t = tk.Frame(self.root, bg="#15244a", highlightthickness=1, highlightbackground=ACCENT)
        tk.Label(t, text=text, bg="#15244a", fg="white", font=("Helvetica", 10, "bold"),
                 wraplength=max(180, self.root.winfo_width() - self.px(140)),
                 justify="left").pack(side="left", padx=14, pady=9)
        if action:
            label, fn = action
            HoverButton(t, label, lambda: (fn(), self.hide_toast()), bg="#15244a",
                        fg=GOLD, padx=10, pady=4).pack(side="left", padx=(0, 8))
        t.place(relx=0.5, rely=1.0, y=10, anchor="s")
        t.lift()
        self.toast_widget = t

        def slide(i=0):   # glide up from below the edge
            if self.toast_widget is not t:
                return
            k = i / 8
            t.place_configure(y=-26 + int(36 * (1 - k) ** 3))
            if i < 8:
                self.root.after(14, slide, i + 1)

        slide()
        self.toast_job = self.root.after(3800, self.hide_toast)

    def hide_toast(self):
        if self.toast_job:
            try:
                self.root.after_cancel(self.toast_job)
            except tk.TclError:
                pass
            self.toast_job = None
        if self.toast_widget is not None:
            self.toast_widget.destroy()
            self.toast_widget = None

    # ------------------------------------------------------------ the clock + alarm engine
    def show_alarm(self, s, kind):
        self.wake_up()                    # bring the planner back when something rings
        AlarmPopup(self, s, kind)

    def tick(self):
        now = datetime.now()
        self.set_pair(self.clock_items, now.strftime("%H:%M:%S"))
        self.set_pair(self.date_items, now.strftime("%A, %B %d, %Y"))
        changed = False

        for s in self.schedules:
            if s["done"]:
                continue
            dt = self.when(s)

            # 1) "near time" reminder
            if (s["remind"] > 0 and not s["reminded"]
                    and now >= dt - timedelta(minutes=s["remind"])):
                s["reminded"] = True
                changed = True
                if now < dt:
                    self.show_alarm(s, "reminder")

            # 2) "it's time" alarm
            if not s["alerted"] and now >= dt:
                s["alerted"] = True
                s["reminded"] = True
                changed = True
                if now - dt <= timedelta(minutes=MISSED_AFTER_MIN):
                    self.show_alarm(s, "due")

            # 3) snooze finished
            snooze = s.get("snooze_until")
            if snooze:
                try:
                    over = now >= datetime.strptime(snooze, SNOOZE_FORMAT)
                except ValueError:
                    over = True
                if over:
                    s["snooze_until"] = ""
                    changed = True
                    self.show_alarm(s, "snoozed")

        if changed:
            self.save()
        self.check_idle()

        # table: rebuild only if a status changed, otherwise just update countdown cells
        new_status = {s["id"]: self.status_of(s, now) for s in self.schedules}
        if new_status != self.status_cache:
            self.refresh_table()
        else:
            for iid in self.tree.get_children():
                s = self.by_id(iid)
                if s:
                    self.tree.set(iid, "left", self.countdown(s, now))

        upcoming = [s for s in self.schedules if not s["done"] and self.when(s) > now]
        if upcoming:
            nxt = min(upcoming, key=lambda x: x["when"])
            self.set_pair(self.next_items,
                          f"⏭  Next: {nxt['title']}  ·  {self.countdown(nxt, now)}")
        else:
            self.set_pair(self.next_items, "No upcoming schedules")

        self.root.after(1000 - now.microsecond // 1000 + 5, self.tick)   # stay on the second


if __name__ == "__main__":
    root = tk.Tk()
    ScheduleApp(root)
    root.mainloop()