"""
Schedule Planner  -  night-drive edition  (v5)
==============================================
A schedule information system with reminders, loud alarms, a moving video
background and a loading screen.

Setup (one time):
    pip install pillow opencv-python
Run:
    python schedule_system.py
    (keep background.mp4 - or any .mp4 / space.jpg - in the same folder)

New in this version
  * THE VIDEO SHOWS THROUGH THE MAIN INTERFACE: the form and the schedule list
    are drawn straight on the picture - labels float over the moving video and
    every schedule is its own card - instead of sitting on a solid panel.
    Settings -> Background -> "Panel opacity" tunes how much of the video shows.
  * ORIGINAL SIZE IS A SETTING: Settings -> Window lets you pick Automatic, a
    preset or your own width x height, "Use current size", "Apply now" and
    "Go to original size" (also Ctrl+0 / double-click the title)
  * The button click sound has been removed.

Still here: loading screen, video background, loud long alarms, 10 alarm sounds,
per-schedule sounds, snooze, undo, filters, calendar picker, adaptive layout.

Shortcuts:  Enter = save   Del = delete   Ctrl+N = new   Ctrl+F = search
            Up/Down = move through the list   Ctrl+0 = original window size
            F11 = fullscreen   Esc = cancel edit / leave fullscreen
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
import traceback
import uuid
import wave
from datetime import date, datetime, timedelta
from datetime import time as dtime
import tkinter.font as tkfont
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
SPLASH_BG = "#05070f"


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

    wide     >= 940 px : form on the left, schedule list on the right
    compact  <  940 px : one panel at a time, switched with the tab buttons
    tiny     <  480 px : same as compact with smaller header and icon-only tabs
    """
    px = lambda n: int(n * sc)
    compact = W < px(940)
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

    def glass(self, w, h, opacity=140):
        key = (w, h, opacity)
        if key not in self._glass:
            if len(self._glass) > 8:
                self._glass.clear()
            alpha = Image.new("L", (w, h), 0)
            ImageDraw.Draw(alpha).rounded_rectangle((0, 0, w - 1, h - 1), radius=18, fill=opacity)
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

    def apply(self, frame, boxes, top, bottom, opacity=140):
        W, H = frame.size
        top_mask, bot_mask = self.fade_masks(W, top, bottom)
        frame.paste((4, 8, 18), (0, 0, W, top_mask.size[1]), top_mask)
        frame.paste((4, 8, 18), (0, H - bot_mask.size[1], W, H), bot_mask)
        for x0, y0, x1, y1 in boxes:
            w, h = x1 - x0, y1 - y0
            if w < 20 or h < 20 or y0 >= H or y1 <= 0:
                continue
            rgb, alpha = self.glass(w, h, opacity)
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
        self.glass_alpha = 140
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

    def set_glass(self, percent):
        """How solid the glass panels are (percent) - lower shows more video."""
        self.glass_alpha = int(255 * max(10, min(100, percent)) / 100)
        with self.lock:
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
            opacity = self.glass_alpha
            self.dirty = False
        if size[0] < 50 or size[1] < 50:
            return
        try:
            frame = self.source.read(size) if advance else self.source.current(size)
        except Exception:
            frame = None
        if frame is None:
            return
        self.overlay.apply(frame, boxes, top, bottom, opacity)
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
    "panel_opacity": 55,     # how solid the glass behind the interface is (%)
    "win_w": 0,              # original window size; 0 x 0 = automatic (fits the screen)
    "win_h": 0,
    "show_splash": True,
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



def find_audio_cmd():
    """A command-line player for macOS / Linux (None if there isn't one)."""
    for cmd in (["afplay"], ["paplay"], ["aplay", "-q"], ["play", "-q"],
                ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"]):
        if shutil.which(cmd[0]):
            return cmd
    return None


class SoundPlayer:
    """Loops a .wav for a set time without freezing the window.

    Windows: winsound (async + loop).  macOS: afplay.  Linux: paplay / aplay / sox / ffplay.
    Falls back to the system bell if nothing else is available.
    """

    def __init__(self, root):
        self.root = root
        self.is_win = sys.platform.startswith("win")
        self.cmd = None if self.is_win else find_audio_cmd()
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
    """Tabbed settings (Sound / Background / Window), sized to fit any screen."""

    TABS = [("sound", "🔊 Sound", "🔊"), ("background", "🎬 Background", "🎬"),
            ("window", "🖥 Window", "🖥")]

    def __init__(self, app, tab="sound"):
        super().__init__(app.root)
        self.app = app
        st = app.settings
        self.custom_path = st["custom_path"]
        self.bg_path = st["background"]
        self.title("Settings")
        self.configure(bg=CARD)
        self.transient(app.root)
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = min(app.px(480), sw - 24), min(app.px(700), sh - 80)
        self.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 4)}")
        self.minsize(min(w, 280), min(h, 320))
        self.wrap = max(180, w - 70)

        # bottom bar first, so Save / Close stay visible on any screen
        bar = tk.Frame(self, bg=CARD)
        bar.pack(side="bottom", fill="x", padx=18, pady=(8, 14))
        HoverButton(bar, "Save", self.save, bg=ACCENT, pady=9, pulse=True).pack(
            side="left", fill="x", expand=True)
        HoverButton(bar, "Close", self.close, pady=9).pack(side="left", padx=(8, 0))

        head = tk.Frame(self, bg=CARD)
        head.pack(side="top", fill="x", padx=18, pady=(14, 0))
        tk.Label(head, text="⚙ Settings", bg=CARD, fg="white",
                 font=("Helvetica", 15, "bold")).pack(anchor="w")
        tabs = tk.Frame(head, bg=CARD)
        tabs.pack(fill="x", pady=(10, 0))
        self.tab_btns = {}
        for key, full, icon in self.TABS:
            b = HoverButton(tabs, icon if w < 380 else full, lambda k=key: self.show_tab(k),
                            padx=10, pady=5, font=("Helvetica", 9, "bold"))
            b.pack(side="left", padx=(0, 6))
            self.tab_btns[key] = b

        self.scroller = ScrollFrame(self)
        self.scroller.pack(side="top", fill="both", expand=True)
        self.pages = {k: tk.Frame(self.scroller.inner, bg=CARD) for k, _, _ in self.TABS}
        self.build_sound(self.pages["sound"])
        self.build_background(self.pages["background"])
        self.build_window(self.pages["window"])

        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self.show_tab(tab)
        self.focus_set()
        self.update_size_label()

    # ---- helpers
    def label(self, parent, text):
        tk.Label(parent, text=text.upper(), bg=CARD, fg=MUTED,
                 font=("Helvetica", 8, "bold")).pack(anchor="w", pady=(14, 4))

    def slider(self, parent, var, lo, hi):
        row = tk.Frame(parent, bg=CARD)
        row.pack(fill="x")
        lbl = tk.Label(row, text=f"{var.get()}%", bg=CARD, fg="white", width=5,
                       font=("Helvetica", 11, "bold"))
        lbl.pack(side="right")
        tk.Scale(row, from_=lo, to=hi, orient="horizontal", variable=var, showvalue=False,
                 bg=CARD, fg=TEXT, troughcolor=INPUT, highlightthickness=0, bd=0,
                 activebackground=ACCENT, sliderrelief="flat",
                 command=lambda v: lbl.configure(text=f"{int(float(v))}%")).pack(
            side="left", fill="x", expand=True)

    def check(self, parent, text, var):
        tk.Checkbutton(parent, text=text, variable=var, bg=CARD, fg=TEXT, selectcolor=INPUT,
                       activebackground=CARD, activeforeground=TEXT, highlightthickness=0,
                       bd=0, font=("Helvetica", 10)).pack(anchor="w", pady=(8, 0))

    def show_tab(self, key):
        for k, page in self.pages.items():
            page.pack_forget()
            self.tab_btns[k].set_base(ACCENT if k == key else BTN)
        self.pages[key].pack(fill="x", padx=18, pady=(2, 16))
        self.scroller.canvas.yview_moveto(0)
        self.scroller._update()

    @staticmethod
    def snooze_text(n):
        return f"{n} minute" + ("" if n == 1 else "s")

    # ---- Sound tab
    def build_sound(self, page):
        st = self.app.settings
        self.label(page, "Alarm sound  (rings when the time arrives)")
        lf = tk.Frame(page, bg=CARD)
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

        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x", pady=(8, 0))
        HoverButton(row, "▶ Test", self.test_alarm, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "■ Stop", self.app.player.stop, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "📂 File…", self.choose_file, padx=10, pady=5).pack(side="left")
        self.custom_lbl = tk.Label(page, bg=CARD, fg=MUTED, font=("Helvetica", 9),
                                   anchor="w", justify="left", wraplength=self.wrap)
        self.custom_lbl.pack(fill="x", pady=(6, 0))
        self.update_custom_label()

        self.label(page, "Reminder sound  (a little before the time)")
        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x")
        self.rem_var = tk.StringVar(value=st["reminder_sound"])
        ttk.Combobox(row, textvariable=self.rem_var, state="readonly", width=18,
                     values=ALL_SOUNDS).pack(side="left")
        HoverButton(row, "▶", self.test_reminder, padx=10, pady=4).pack(side="left", padx=(8, 0))

        self.label(page, "Alarm volume")
        self.vol = tk.IntVar(value=st["volume"])
        self.slider(page, self.vol, 20, 100)

        self.label(page, "Ring for")
        current = next((t for t, s in RING_CHOICES if s == st["ring_seconds"]), "2 minutes")
        self.ring_var = tk.StringVar(value=current)
        ttk.Combobox(page, textvariable=self.ring_var, state="readonly", width=20,
                     values=[t for t, _ in RING_CHOICES]).pack(anchor="w")

        self.label(page, "Snooze length")
        self.snooze_var = tk.StringVar(value=self.snooze_text(st["snooze_min"]))
        ttk.Combobox(page, textvariable=self.snooze_var, state="readonly", width=20,
                     values=[self.snooze_text(n) for n in SNOOZE_CHOICES]).pack(anchor="w")

        tk.Label(page, text="Tip: your device's own volume still applies — turn it up for the "
                            "loudest alarm.", bg=CARD, fg=MUTED, font=("Helvetica", 9),
                 justify="left", anchor="w", wraplength=self.wrap).pack(fill="x", pady=(14, 0))

    # ---- Background tab
    def build_background(self, page):
        st = self.app.settings
        self.label(page, "Background video or picture")
        self.bg_lbl = tk.Label(page, bg=CARD, fg=MUTED, font=("Helvetica", 9),
                               anchor="w", justify="left", wraplength=self.wrap)
        self.bg_lbl.pack(fill="x")
        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x", pady=(6, 0))
        HoverButton(row, "🎬 Choose…", self.choose_bg, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "↺ Default", self.reset_bg, padx=10, pady=5).pack(side="left")
        self.update_bg_label()

        self.bg_play = tk.BooleanVar(value=st["bg_play"])
        self.check(page, "Play the animated background", self.bg_play)

        self.label(page, "Panel opacity  (lower = more video shows through)")
        self.opacity = tk.IntVar(value=st["panel_opacity"])
        self.slider(page, self.opacity, 20, 100)

        self.label(page, "Smoothness")
        cur_fps = next((t for t, f in FPS_CHOICES if f == st["bg_fps"]), FPS_CHOICES[1][0])
        self.fps_var = tk.StringVar(value=cur_fps)
        ttk.Combobox(page, textvariable=self.fps_var, state="readonly", width=22,
                     values=[t for t, _ in FPS_CHOICES]).pack(anchor="w")

        self.label(page, "Scenery mode  (panels slide away when idle)")
        cur_idle = next((t for t, n in IDLE_CHOICES if n == st["idle_hide"]), "After 1 minute")
        self.idle_var = tk.StringVar(value=cur_idle)
        ttk.Combobox(page, textvariable=self.idle_var, state="readonly", width=22,
                     values=[t for t, _ in IDLE_CHOICES]).pack(anchor="w")

    # ---- Window tab
    SIZE_PRESETS = [("Automatic (fits my screen)", (0, 0)), ("Compact · 800 × 560", (800, 560)),
                    ("Standard · 1120 × 720", (1120, 720)), ("Large · 1400 × 880", (1400, 880)),
                    ("Custom", None)]

    def build_window(self, page):
        app, st = self.app, self.app.settings
        self.label(page, "Window size now")
        self.size_lbl = tk.Label(page, bg=CARD, fg=TEXT, font=("Helvetica", 10),
                                 anchor="w", justify="left", wraplength=self.wrap)
        self.size_lbl.pack(fill="x")

        self.label(page, "Original size  (what “Reset” returns to)")
        self.preset_var = tk.StringVar(value=self.preset_for(st["win_w"], st["win_h"]))
        cb = ttk.Combobox(page, textvariable=self.preset_var, state="readonly", width=26,
                          values=[n for n, _ in self.SIZE_PRESETS])
        cb.pack(anchor="w")
        cb.bind("<<ComboboxSelected>>", self.on_preset)

        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x", pady=(10, 0))
        w0, h0 = app.original_size
        self.w_var, self.h_var = tk.StringVar(value=str(w0)), tk.StringVar(value=str(h0))
        self._filling = False
        for text, var, hi in (("Width", self.w_var, 8000), ("", None, 0), ("Height", self.h_var, 8000)):
            if var is None:
                tk.Label(row, text="×", bg=CARD, fg=MUTED, font=("Helvetica", 12)).pack(side="left", padx=6)
                continue
            tk.Label(row, text=text, bg=CARD, fg=MUTED, font=("Helvetica", 9)).pack(side="left", padx=(0, 4))
            tk.Spinbox(row, from_=320 if text == "Width" else 460, to=hi, width=6, textvariable=var,
                       bg=INPUT, fg=TEXT, buttonbackground=BTN, insertbackground=TEXT, relief="flat",
                       highlightthickness=1, highlightbackground=EDGE, highlightcolor=ACCENT,
                       font=("Helvetica", 11)).pack(side="left")
            var.trace_add("write", self.on_size_typed)

        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x", pady=(10, 0))
        HoverButton(row, "📏 Use current size", self.use_current, padx=10, pady=5).pack(
            side="left", padx=(0, 6))
        HoverButton(row, "▶ Apply now", self.apply_now, padx=10, pady=5).pack(side="left")
        row = tk.Frame(page, bg=CARD)
        row.pack(fill="x", pady=(8, 0))
        HoverButton(row, "↺ Go to original size", self.reset_size, padx=10, pady=5).pack(side="left", padx=(0, 6))
        HoverButton(row, "⛶ Fullscreen", app.toggle_fullscreen, padx=10, pady=5).pack(side="left")
        tk.Label(page, text="Press Save to keep a new original size.", bg=CARD, fg=MUTED,
                 font=("Helvetica", 9), anchor="w").pack(fill="x", pady=(6, 0))

        self.label(page, "Startup")
        self.splash_var = tk.BooleanVar(value=st["show_splash"])
        self.check(page, "Show the loading screen when the app starts", self.splash_var)

        tk.Label(page, text="Drag the window edges to any size and the layout adapts. "
                            "Ctrl+0 (or a double-click on the title) returns to the original size; "
                            "F11 toggles fullscreen.", bg=CARD, fg=MUTED, font=("Helvetica", 9),
                 justify="left", anchor="w", wraplength=self.wrap).pack(fill="x", pady=(16, 0))

    def preset_for(self, w, h):
        for name, size in self.SIZE_PRESETS:
            if size == (w, h):
                return name
        return "Custom"

    def set_fields(self, w, h):
        self._filling = True
        self.w_var.set(str(w))
        self.h_var.set(str(h))
        self._filling = False

    def on_preset(self, _e=None):
        size = dict(self.SIZE_PRESETS)[self.preset_var.get()]
        if size is None:
            return
        self.set_fields(*(self.app.auto_size() if size == (0, 0) else size))

    def on_size_typed(self, *_):
        if not self._filling:
            self.preset_var.set("Custom")

    def chosen_size(self):
        try:
            return self.app.clamp_size(int(self.w_var.get()), int(self.h_var.get()))
        except (TypeError, ValueError):
            return None

    def use_current(self):
        r = self.app.root
        self.set_fields(r.winfo_width(), r.winfo_height())
        self.preset_var.set("Custom")

    def apply_now(self):
        size = self.chosen_size()
        if size:
            self.app.resize_window(*size)
        else:
            self.app.toast("Width and height must be numbers")

    def update_size_label(self):
        if not self.winfo_exists():
            return
        r, ow, oh = self.app.root, *self.app.original_size
        self.size_lbl.configure(
            text=f"Now: {r.winfo_width()} × {r.winfo_height()}   ·   layout: {self.app.mode}\n"
                 f"Original (saved): {ow} × {oh}")
        self.after(500, self.update_size_label)

    def reset_size(self):
        self.app.reset_window_size()

    # ---- actions
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
            self.show_tab("sound")
            return
        size = self.chosen_size()
        if size is None:
            self.app.toast("Width and height must be numbers")
            self.show_tab("window")
            return
        auto = self.preset_var.get() == self.SIZE_PRESETS[0][0]
        win = (0, 0) if auto else size
        st = self.app.settings
        bg_changed = st["background"] != self.bg_path
        size_changed = (st["win_w"], st["win_h"]) != win
        st.update(alarm_sound=name, reminder_sound=self.rem_var.get(),
                  volume=int(self.vol.get()),
                  ring_seconds=dict(RING_CHOICES)[self.ring_var.get()],
                  snooze_min=int(self.snooze_var.get().split()[0]),
                  custom_path=self.custom_path, background=self.bg_path,
                  bg_play=bool(self.bg_play.get()),
                  bg_fps=dict(FPS_CHOICES)[self.fps_var.get()],
                  idle_hide=dict(IDLE_CHOICES)[self.idle_var.get()],
                  panel_opacity=int(self.opacity.get()),
                  win_w=win[0], win_h=win[1],
                  show_splash=bool(self.splash_var.get()))
        self.app.save_settings()
        self.app.pregenerate()
        self.app.apply_background_settings(restart=bg_changed)
        self.app.original_size = self.app.compute_original_size()
        if size_changed:                      # a new original size takes effect straight away
            self.app.resize_window(*self.app.original_size)
        self.app.toast("Settings saved ✓")
        self.close()

    def close(self):
        self.app.player.stop()
        self.app.settings_dialog = None
        self.destroy()


# ================================================================ loading screen
def load_still(path):
    """A single picture for the loading-screen backdrop: a video frame or an image."""
    if not (HAS_PIL and path):
        return None
    ext = os.path.splitext(path)[1].lower()
    try:
        if ext in VIDEO_EXT and HAS_CV2:
            cap = cv2.VideoCapture(path)
            n = cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0
            if n > 10:
                cap.set(cv2.CAP_PROP_POS_FRAMES, min(30, int(n // 3)))   # early frame = fast to decode
            ok, frame = cap.read()
            cap.release()
            if not ok:
                return None
            h, w = frame.shape[:2]
            if w > 1280:
                frame = cv2.resize(frame, (1280, int(h * 1280 / w)), interpolation=cv2.INTER_AREA)
            return Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
        if ext in IMAGE_EXT:
            return Image.open(path).convert("RGB")
    except Exception:
        pass
    return None


def ease_out(k):
    return 1 - (1 - k) ** 3


def ease_in_out(k):
    return 4 * k ** 3 if k < 0.5 else 1 - (-2 * k + 2) ** 3 / 2


class Splash(tk.Frame):
    """Animated loading screen drawn over the whole window.

    While the app really loads behind it, it shows falling rain, a spinning ring,
    a progress bar and rotating tips.  finish() plays the exit: a pulse, then the
    whole screen lifts away like a curtain to reveal the app.
    """

    TIPS = [
        "Tip: press Ctrl+N to start a new schedule",
        "Tip: double-click a schedule to edit it",
        "Tip: every schedule can have its own alarm sound",
        "Tip: Snooze buys you a few more minutes",
        "Tip: the panels slide away when you're idle — move the mouse to bring them back",
        "Tip: F11 = fullscreen, Ctrl+0 = back to the original window size",
    ]

    def __init__(self, app):
        super().__init__(app.root, bg=SPLASH_BG)
        self.app = app
        self.place(x=0, y=0, relwidth=1, relheight=1)
        self.cv = cv = tk.Canvas(self, bg=SPLASH_BG, highlightthickness=0)
        cv.pack(fill="both", expand=True)
        self.W = self.H = 0
        self.u = 1.0
        self.target = self.disp = 0.0
        self.t = 0.0
        self.alive = True
        self.phase = "loading"
        self.phase_t0 = 0.0
        self.fade_all = 1.0
        self.msg_fade = 0.0
        self.tip_i = random.randrange(len(self.TIPS))
        self.tip_fade = 0.0
        self.tip_t = time.time()
        self.on_reveal = self.on_done = None
        self.ring = (0, 0, 40)
        self.bar = (0, 1, 0)

        # the backdrop is grabbed on a worker thread so the loading screen appears instantly
        self.still = None
        self._still_box = []
        self._still_done = False
        self.backdrop_fade = 0.0
        path = app.first_background_path()
        threading.Thread(target=lambda: self._still_box.append(load_still(path)),
                         daemon=True).start()
        self.bg_photo = None
        self._bg_job = None
        self.bg_item = cv.create_image(0, 0, anchor="nw")

        rnd = random.Random(3)
        self.rain = [{"fx": rnd.random(), "fy": rnd.random(), "v": rnd.uniform(0.9, 2.3),
                      "l": rnd.uniform(0.03, 0.08), "b": rnd.uniform(0.35, 1.0),
                      "id": cv.create_line(0, 0, 0, 0, width=1)} for _ in range(48)]
        self.pulse = cv.create_oval(0, 0, 0, 0, outline=ACCENT, width=2, state="hidden")
        self.arcs = [cv.create_arc(0, 0, 0, 0, start=0, extent=80, style="arc", outline=c, width=3)
                     for c in (ACCENT, "#7fb0ff", "#2a4f9e")]
        self.icon = cv.create_text(0, 0, text="⏰", font=("Helvetica", 26), fill="#ffffff")
        self.title = self._pair("S C H E D U L E   P L A N N E R", ("Helvetica", 28, "bold"))
        self.sub = self._pair("Plan it. Get reminded. Never miss a moment.", ("Helvetica", 11))
        self.track = cv.create_line(0, 0, 0, 0, width=10, capstyle="round", fill="#16213a")
        self.fill = cv.create_line(0, 0, 0, 0, width=10, capstyle="round", fill=ACCENT, state="hidden")
        self.shine = cv.create_line(0, 0, 0, 0, width=4, capstyle="round", fill="#cfe3ff", state="hidden")
        self.pct = cv.create_text(0, 0, text="0%", anchor="e", font=("Helvetica", 10, "bold"), fill=MUTED)
        self.msg_item = cv.create_text(0, 0, text="", font=("Helvetica", 11), fill=MUTED)
        self.tip_item = cv.create_text(0, 0, text=self.TIPS[self.tip_i], font=("Helvetica", 10, "italic"),
                                       fill=FAINT, justify="center")
        self.edge = cv.create_line(0, 0, 0, 0, width=3, fill=ACCENT)   # glowing bottom edge

        cv.bind("<Configure>", self.on_resize)
        self.after(33, self.tick)

    # ---- drawing helpers
    def _pair(self, text, font):
        sh = self.cv.create_text(0, 0, text=text, font=font, fill="#000000")
        mn = self.cv.create_text(0, 0, text=text, font=font, fill="#ffffff")
        return sh, mn

    def _put(self, pair, x, y):
        self.cv.coords(pair[0], x + 1, y + 2)
        self.cv.coords(pair[1], x, y)

    def _font(self, item, size, bold=False, italic=False):
        style = " ".join(x for x in ("bold" if bold else "", "italic" if italic else "") if x)
        self.cv.itemconfigure(item, font=("Helvetica", max(7, int(size * self.u)), *([style] if style else [])))

    def on_resize(self, e):
        W, H = e.width, e.height
        if W < 50 or H < 50:
            return
        self.W, self.H = W, H
        u = self.u = max(0.55, min(1.3, min(W / 800, H / 560)))
        cx, cy = W / 2, H * 0.42
        r = 46 * u
        self.ring = (cx, cy - 78 * u, r)
        for i, arc in enumerate(self.arcs):
            rr = r - i * 9 * u
            self.cv.coords(arc, cx - rr, self.ring[1] - rr, cx + rr, self.ring[1] + rr)
        self.cv.coords(self.icon, cx, self.ring[1])
        self._font(self.icon, 26)
        wide_title = W >= 560
        for it in self.title:
            self.cv.itemconfigure(it, text="S C H E D U L E   P L A N N E R" if wide_title else "SCHEDULE PLANNER")
            self._font(it, 28 if wide_title else 24, bold=True)
        self._put(self.title, cx, cy + 22 * u)
        for it in self.sub:
            self._font(it, 11)
        self._put(self.sub, cx, cy + 58 * u)
        bw = min(460 * u, W * 0.78)
        self.bar = (cx - bw / 2, cx + bw / 2, cy + 112 * u)
        self.cv.itemconfigure(self.track, width=max(6, int(10 * u)))
        self.cv.itemconfigure(self.fill, width=max(6, int(10 * u)))
        self.cv.coords(self.track, self.bar[0], self.bar[2], self.bar[1], self.bar[2])
        self.cv.coords(self.pct, self.bar[1], self.bar[2] - 20 * u)
        self._font(self.pct, 10, bold=True)
        self.cv.coords(self.msg_item, cx, self.bar[2] + 30 * u)
        self._font(self.msg_item, 11)
        self.cv.coords(self.tip_item, cx, H - 38 * u)
        self.cv.itemconfigure(self.tip_item, width=int(W * 0.86))
        self._font(self.tip_item, 10, italic=True)
        self.cv.coords(self.edge, 0, H - 1, W, H - 1)
        if self._bg_job:
            self.after_cancel(self._bg_job)
        self._bg_job = self.after(70, self.rebuild_bg)

    def rebuild_bg(self):
        self._bg_job = None
        if self.still is None or self.W < 50:
            return
        img = cover_fit(self.still, (self.W, self.H))
        # starts almost black and brightens to the final look (a gentle fade-in)
        dark = 1 - (1 - 0.58) * ease_out(min(1.0, self.backdrop_fade))
        img = Image.blend(img, Image.new("RGB", img.size, (4, 8, 18)), dark)
        self.bg_photo = ImageTk.PhotoImage(img)
        self.cv.itemconfigure(self.bg_item, image=self.bg_photo)

    # ---- called by the app while it loads
    def set_message(self, text):
        self.cv.itemconfigure(self.msg_item, text=text)
        self.msg_fade = 0.0

    def set_progress(self, p):
        self.target = max(self.target, min(1.0, p))

    def finish(self, on_reveal, on_done):
        """Bar to 100%, a pulse, the curtain lifts - on_reveal fires as it starts to lift."""
        self.on_reveal, self.on_done = on_reveal, on_done
        self.target = 1.0
        self.set_message("Ready  ✓")
        self.phase, self.phase_t0 = "ready", time.time()
        self.cv.itemconfigure(self.pulse, state="normal")

    # ---- animation
    def tick(self):
        if not self.alive:
            return
        cv, u, W, H = self.cv, self.u, self.W, self.H
        now = time.time()
        self.t += 0.033
        if self._still_box and not self._still_done:      # the worker thread finished
            self._still_done, self.still = True, self._still_box[0]
            self.backdrop_fade = 0.0
        if self.still is not None and self.backdrop_fade < 1.0 and W > 50:
            self.backdrop_fade += 0.07
            self.rebuild_bg()
        if W > 50:
            # progress eases toward its target
            self.disp += (self.target - self.disp) * 0.09
            if abs(self.target - self.disp) < 0.0015:
                self.disp = self.target
            x0, x1, y = self.bar
            fx = x0 + (x1 - x0) * self.disp
            if self.disp > 0.012:
                cv.coords(self.fill, x0, y, fx, y)
                cv.itemconfigure(self.fill, state="normal")
                sx = x0 + ((self.t * 0.55) % 1.5 - 0.25) * (x1 - x0)
                a, b = max(x0, sx - 34 * u), min(fx, sx + 34 * u)
                if b - a > 4:
                    cv.coords(self.shine, a, y - 1, b, y - 1)
                    cv.itemconfigure(self.shine, state="normal")
                else:
                    cv.itemconfigure(self.shine, state="hidden")
            cv.itemconfigure(self.pct, text=f"{int(self.disp * 100)}%")

            # spinner
            for i, arc in enumerate(self.arcs):
                d = 1 if i % 2 == 0 else -1
                cv.itemconfigure(arc, start=(d * self.t * (210 + 80 * i) + i * 120) % 360,
                                 extent=60 + 35 * math.sin(self.t * 2 + i))

            # rain
            for r in self.rain:
                r["fy"] += r["v"] * 9 * u / H
                r["fx"] -= r["v"] * 9 * u * 0.2 / W
                if r["fy"] > 1.05 or r["fx"] < -0.05:
                    r["fy"], r["fx"] = -r["l"], random.random() * 1.15
                x, yy, ln = r["fx"] * W, r["fy"] * H, r["l"] * H
                cv.coords(r["id"], x, yy, x - ln * 0.2, yy + ln)
                cv.itemconfigure(r["id"], fill=mix(SPLASH_BG, "#6f8fc9", r["b"] * 0.8 * self.fade_all))

            # text fades / rotating tips
            self.msg_fade = min(1.0, self.msg_fade + 0.08)
            f = self.fade_all
            cv.itemconfigure(self.msg_item, fill=mix(SPLASH_BG, "#cfe0ff", self.msg_fade * f))
            cv.itemconfigure(self.pct, fill=mix(SPLASH_BG, MUTED, f))
            cv.itemconfigure(self.title[1], fill=mix(SPLASH_BG, "#ffffff", f))
            cv.itemconfigure(self.sub[1], fill=mix(SPLASH_BG, "#cfe0ff", f))
            cv.itemconfigure(self.icon, fill=mix(SPLASH_BG, "#ffffff", f))
            cv.itemconfigure(self.track, fill=mix(SPLASH_BG, "#16213a", f))
            cv.itemconfigure(self.fill, fill=mix(SPLASH_BG, ACCENT, f))
            if now - self.tip_t > 2.8 and self.phase == "loading":
                self.tip_i = (self.tip_i + 1) % len(self.TIPS)
                cv.itemconfigure(self.tip_item, text=self.TIPS[self.tip_i])
                self.tip_fade, self.tip_t = 0.0, now
            self.tip_fade = min(1.0, self.tip_fade + 0.05)
            cv.itemconfigure(self.tip_item, fill=mix(SPLASH_BG, "#7d8fb8", self.tip_fade * f))

            self.run_phase(now)
        self.after(33, self.tick)

    def run_phase(self, now):
        cv, W, H = self.cv, self.W, self.H
        if self.phase == "ready":
            k = min(1.0, (now - self.phase_t0) / 0.75)
            cx, cy, r = self.ring
            R = r * (1 + 3.4 * ease_out(k))
            cv.coords(self.pulse, cx - R, cy - R, cx + R, cy + R)
            cv.itemconfigure(self.pulse, outline=mix(ACCENT, SPLASH_BG, k))
            self.fade_all = 1 - max(0.0, (k - 0.3) / 0.7)
            if k >= 1.0 and self.disp >= 0.999:
                self.phase, self.phase_t0 = "lift", now
                cv.itemconfigure(self.pulse, state="hidden")
                if self.on_reveal:
                    self.on_reveal()          # the panels start to glide in as the curtain lifts
        elif self.phase == "lift":
            k = min(1.0, (now - self.phase_t0) / 0.95)
            self.place_configure(y=-int(H * ease_in_out(k)))
            if k >= 1.0:
                self.alive = False
                self.destroy()
                if self.on_done:
                    self.on_done()


# ================================================================ interface drawn on the canvas
def rrect_points(x0, y0, x1, y1, r):
    """Corner points for a rounded rectangle (use with create_polygon(smooth=True))."""
    r = max(1, min(r, (x1 - x0) // 2, (y1 - y0) // 2))
    return [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
            x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]


class CText:
    """Text drawn straight on the canvas, with a soft shadow.  It has no background of its
    own, so the moving video shows through behind it."""

    def __init__(self, canvas, text="", size=10, bold=False, italic=False, fill=TEXT, width=0):
        self.c = canvas
        self.text = text
        self.font = tkfont.Font(family="Helvetica", size=size,
                                weight="bold" if bold else "normal",
                                slant="italic" if italic else "roman")
        opts = dict(text=text, font=self.font, anchor="nw", width=width, state="hidden")
        self.shadow = canvas.create_text(0, 0, fill="#000000", **opts)
        self.main = canvas.create_text(0, 0, fill=fill, **opts)
        self.ids = [self.shadow, self.main]

    def configure(self, text=None, wraplength=None, fg=None):
        for i in self.ids:
            if text is not None:
                self.c.itemconfigure(i, text=text)
            if wraplength is not None:
                self.c.itemconfigure(i, width=wraplength)
        if text is not None:
            self.text = text
        if fg is not None:
            self.c.itemconfigure(self.main, fill=fg)

    def place(self, x, y):
        self.c.coords(self.shadow, x + 1, y + 1)
        self.c.coords(self.main, x, y)

    def size(self):
        lines = self.text.split("\n") or [""]
        return (max(self.font.measure(t) for t in lines),
                self.font.metrics("linespace") * len(lines))

    def show(self, on):
        for i in self.ids:
            self.c.itemconfigure(i, state="normal" if on else "hidden")


class FormView:
    """The 'new schedule' form: labels and input widgets arranged in rows right on the canvas.

    Rows that do not fit are hidden and the mouse wheel scrolls row by row, so the form works
    in any window size.  Each row is a list of items:  ("t", CText)  or  ("w", id, widget, width, height)
    where width is "fill", "nat" (the widget's natural width) or a number of pixels.
    """

    def __init__(self, app):
        self.app, self.c = app, app.canvas
        self.rows = []
        self.box = (0, 0, 10, 10)
        self.shift = 0
        self.visible = True
        self.first = 0
        self.max_first = 0
        self.ids = []
        self.track = self.c.create_line(0, 0, 0, 0, width=3, fill="#1b2a4d", capstyle="round", state="hidden")
        self.thumb = self.c.create_line(0, 0, 0, 0, width=3, fill="#4f6fb3", capstyle="round", state="hidden")

    def t(self, ctext):
        return ("t", ctext)

    def w(self, widget, width="nat", height=None):
        wid = self.c.create_window(0, 0, window=widget, anchor="nw", state="hidden")
        self.ids.append(wid)
        return ("w", wid, widget, width, height)

    def row(self, height, items, top=0, gap=None):
        self.rows.append({"h": height, "items": items, "top": top, "gap": gap})

    # ---- geometry
    def set_geometry(self, box, shift):
        self.box, self.shift = box, shift
        self.relayout()

    def set_visible(self, visible):
        self.visible = visible
        self.relayout()

    def scroll_by(self, n):
        first = max(0, min(self.first + n, self.max_first))
        if first != self.first:
            self.first = first
            self.relayout()

    def _hide(self, row):
        for it in row["items"]:
            if it[0] == "t":
                it[1].show(False)
            else:
                self.c.itemconfigure(it[1], state="hidden")

    def _place(self, row, x, y, width):
        px = self.app.px
        gap = px(6) if row["gap"] is None else row["gap"]
        widths, fills = [], 0
        for it in row["items"]:
            if it[0] == "t":
                widths.append(it[1].size()[0] + px(2))
            elif it[3] == "fill":
                widths.append(None)
                fills += 1
            elif it[3] == "nat":
                widths.append(it[2].winfo_reqwidth())
            else:
                widths.append(int(it[3]))
        fixed = sum(v for v in widths if v is not None) + gap * (len(widths) - 1)
        fill_w = max(px(40), (width - fixed) // fills) if fills else 0
        cx = x
        for it, wd in zip(row["items"], widths):
            wd = fill_w if wd is None else wd
            if it[0] == "t":
                _tw, th = it[1].size()
                it[1].place(cx, y + (row["h"] - th) // 2)
                it[1].show(True)
            else:
                _k, wid, widget, _spec, height = it
                hh = height or widget.winfo_reqheight()
                self.c.coords(wid, cx, y + (row["h"] - hh) // 2)
                self.c.itemconfigure(wid, width=wd, height=hh, state="normal")
            cx += wd + gap

    def relayout(self):
        px, c = self.app.px, self.c
        x0, y0, x1, y1 = self.box
        pad = px(16)
        vtop = y0 + px(12) + self.shift
        vh = (y1 - y0) - px(24)
        ys, y = [], 0
        for r in self.rows:
            y += r["top"]
            ys.append(y)
            y += r["h"]
        total = y
        self.max_first = max(0, len(self.rows) - 1)
        for k, r in enumerate(self.rows):
            if total - (ys[k] - r["top"]) <= vh:      # everything from row k down fits
                self.max_first = k
                break
        self.first = max(0, min(self.first, self.max_first))
        off = (ys[self.first] - self.rows[self.first]["top"]) if self.rows else 0
        scrollable = self.max_first > 0
        iw = x1 - x0 - 2 * pad - (px(8) if scrollable else 0)
        for i, r in enumerate(self.rows):
            top = ys[i] - off
            if self.visible and top >= 0 and top + r["h"] <= vh + 2:
                self._place(r, x0 + pad, vtop + top, iw)
            else:
                self._hide(r)
        if self.visible and scrollable:                 # slim scroll indicator on the right edge
            tx = x1 - px(8)
            tl = max(px(24), int(vh * vh / max(total, 1)))
            ty = vtop + int((vh - tl) * self.first / self.max_first)
            c.coords(self.track, tx, vtop, tx, vtop + vh)
            c.coords(self.thumb, tx, ty, tx, ty + tl)
            c.itemconfigure(self.track, state="normal")
            c.itemconfigure(self.thumb, state="normal")
        else:
            c.itemconfigure(self.track, state="hidden")
            c.itemconfigure(self.thumb, state="hidden")


ROW_BG = "#0b1222"
STATUS_COLORS = {"Overdue": "#ff8aa0", "Due soon": GOLD, "Upcoming": "#7fb0ff", "Done": FAINT}


class ScheduleList:
    """The schedule list: every schedule is a rounded card drawn on the canvas, with video
    showing in the gaps.  Mouse wheel / slim scrollbar / Up-Down keys move through it."""

    COLS = {"date": ("Date", 100), "time": ("Time", 56), "when": ("When", 118),
            "title": ("Title", 0), "left": ("Countdown", 112), "status": ("Status", 84)}

    def __init__(self, app):
        self.app, self.c = app, app.canvas
        px = app.px
        self.row_h, self.head_h = px(38), px(24)
        self.font = tkfont.Font(family="Helvetica", size=10)
        self.head_font = tkfont.Font(family="Helvetica", size=8, weight="bold")
        self.rows = []
        self.sel = self.hover = None
        self.first, self.page = 0, 1
        self.box, self.cols, self.dy = (0, 0, 10, 10), ("title",), 0
        self.visible = True
        self.cells, self.bgs, self.widths = {}, {}, {}
        self.track_geom = None
        c = self.c
        c.tag_bind("lrow", "<Button-1>", self._click)
        c.tag_bind("lrow", "<Double-Button-1>", self._double)
        for seq in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
            c.tag_bind("lrow", seq, self._context)
        c.tag_bind("lrow", "<Enter>", self._enter)
        c.tag_bind("lrow", "<Leave>", self._leave)
        for tag in ("lthumb", "ltrack"):
            c.tag_bind(tag, "<B1-Motion>", self._drag)
            c.tag_bind(tag, "<Button-1>", self._drag)

    # ---- data
    def set_rows(self, rows):
        self.rows = rows
        if self.sel is not None and not self.exists(self.sel):
            self.sel = None
        self.redraw()

    def exists(self, iid):
        return any(r["iid"] == iid for r in self.rows)

    def get_children(self):
        return [r["iid"] for r in self.rows]

    def selection(self):
        return (self.sel,) if self.sel is not None and self.exists(self.sel) else ()

    def selection_set(self, iid):
        self.select(iid)

    def select(self, iid):
        old, self.sel = self.sel, iid
        self._recolor(old)
        self._recolor(iid)
        self.app.show_details()

    def move(self, delta):
        ids = self.get_children()
        if not ids:
            return
        cur = ids.index(self.sel) if self.sel in ids else (-1 if delta > 0 else len(ids))
        new = ids[max(0, min(len(ids) - 1, cur + delta))]
        self.select(new)
        self.see(new)

    def see(self, iid):
        ids = self.get_children()
        if iid not in ids:
            return
        i = ids.index(iid)
        if i < self.first:
            self.first = i
        elif i >= self.first + self.page:
            self.first = i - self.page + 1
        else:
            return
        self.redraw()

    def scroll_by(self, n):
        first = max(0, min(self.first + n, max(0, len(self.rows) - self.page)))
        if first != self.first:
            self.first = first
            self.redraw()

    def set(self, iid, col, text):
        for r in self.rows:
            if r["iid"] == iid:
                if r["vals"].get(col) == text:
                    return
                r["vals"][col] = text
                item = self.cells.get(iid, {}).get(col)
                if item is not None:
                    self.c.itemconfigure(item, text=self.fit(text, self.widths.get(col, 9999)))
                return

    # ---- geometry
    def set_geometry(self, box, cols, dy):
        changed = box != self.box or cols != self.cols
        self.box, self.cols = box, cols
        if changed:
            self.dy = dy
            self.redraw()
        elif dy != self.dy:
            self.c.move("lview", 0, dy - self.dy)
            if self.track_geom:
                y0, y1, th = self.track_geom
                self.track_geom = (y0 + dy - self.dy, y1 + dy - self.dy, th)
            self.dy = dy

    def set_visible(self, visible):
        if visible != self.visible:
            self.visible = visible
            self.redraw()

    # ---- drawing
    def fit(self, text, maxw):
        if self.font.measure(text) <= maxw:
            return text
        while len(text) > 1 and self.font.measure(text + "…") > maxw:
            text = text[:-1]
        return text + "…"

    def colors(self, row, selected, hovered):
        if selected:
            return ACCENT, "#ffffff"
        bg, fg = {"overdue": ("#2a1220", "#ff9bb0"), "soon": ("#2a2410", GOLD),
                  "done": ("#080d19", FAINT)}.get(row["tag"], (ROW_BG, TEXT))
        return (mix(bg, "#ffffff", 0.09) if hovered else bg), fg

    def _cell_color(self, col, row, fg, selected):
        return STATUS_COLORS.get(row["status"], fg) if col == "status" and not selected else fg

    def _row(self, iid):
        return next((r for r in self.rows if r["iid"] == iid), None)

    def _recolor(self, iid):
        row = self._row(iid) if iid is not None else None
        if row is None or iid not in self.bgs:
            return
        sel = iid == self.sel
        bg, fg = self.colors(row, sel, iid == self.hover)
        self.c.itemconfigure(self.bgs[iid], fill=bg)
        for col, item in self.cells[iid].items():
            self.c.itemconfigure(item, fill=self._cell_color(col, row, fg, sel))

    def redraw(self):
        c, px = self.c, self.app.px
        c.delete("lview")
        self.cells.clear()
        self.bgs.clear()
        self.widths.clear()
        self.track_geom = None
        x0, y0, x1, y1 = self.box
        if not self.visible or x1 - x0 < 80 or y1 - y0 < self.head_h + self.row_h:
            return
        top = y0 + self.dy
        total = len(self.rows)
        self.page = max(1, int((y1 - y0 - self.head_h) // self.row_h))
        self.first = max(0, min(self.first, max(0, total - self.page)))
        scroll = total > self.page
        right = x1 - (px(10) if scroll else 0)
        pad, gap = px(12), px(8)
        fixed = sum(self.COLS[k][1] for k in self.cols if k != "title")
        title_w = max(px(70), (right - x0) - 2 * pad - fixed - gap * (len(self.cols) - 1))
        xs, x = {}, x0 + pad
        for k in self.cols:
            self.widths[k] = title_w if k == "title" else self.COLS[k][1]
            xs[k] = x
            x += self.widths[k] + gap
        for k in self.cols:
            c.create_text(xs[k], top + self.head_h // 2, text=self.COLS[k][0].upper(), anchor="w",
                          font=self.head_font, fill=MUTED, tags=("lview",))
        if not self.rows:
            c.create_text((x0 + x1) / 2, top + self.head_h + px(46), text="Nothing here yet ✨",
                          font=("Helvetica", 12), fill=MUTED, tags=("lview",))
        for k in range(self.page):
            idx = self.first + k
            if idx >= total:
                break
            row = self.rows[idx]
            iid = row["iid"]
            ry = top + self.head_h + k * self.row_h
            sel = iid == self.sel
            bg, fg = self.colors(row, sel, iid == self.hover)
            tags = ("lview", "lrow", "i:" + iid)
            self.bgs[iid] = c.create_polygon(
                rrect_points(x0, ry + 2, right, ry + self.row_h - 2, px(9)),
                smooth=True, fill=bg, outline="", tags=tags)
            ids = {}
            for col in self.cols:
                ids[col] = c.create_text(
                    xs[col], ry + self.row_h // 2, text=self.fit(row["vals"].get(col, ""), self.widths[col]),
                    anchor="w", font=self.font, fill=self._cell_color(col, row, fg, sel), tags=tags)
            self.cells[iid] = ids
        if scroll:                                       # slim, draggable scroll bar
            ty0, ty1 = top + self.head_h + px(4), top + (y1 - y0) - px(4)
            th = max(px(24), int((ty1 - ty0) * self.page / total))
            tp = ty0 + int((ty1 - ty0 - th) * self.first / max(1, total - self.page))
            sx = x1 - px(4)
            c.create_line(sx, ty0, sx, ty1, width=px(4), fill="#1b2a4d", capstyle="round",
                          tags=("lview", "ltrack"))
            c.create_line(sx, tp, sx, tp + th, width=px(4), fill="#4f6fb3", capstyle="round",
                          tags=("lview", "lthumb"))
            self.track_geom = (ty0, ty1, th)

    # ---- mouse
    def _iid(self):
        for t in self.c.gettags("current"):
            if t.startswith("i:"):
                return t[2:]
        return None

    def _click(self, _e):
        iid = self._iid()
        if iid is not None:
            self.c.focus_set()
            self.select(iid)

    def _double(self, _e):
        iid = self._iid()
        if iid is not None:
            self.select(iid)
            self.app.edit_selected()

    def _context(self, e):
        iid = self._iid()
        if iid is not None:
            self.select(iid)
            self.app.row_menu(iid, e.x_root, e.y_root)

    def _enter(self, _e):
        iid = self._iid()
        if iid is not None:
            self.hover = iid
            self._recolor(iid)

    def _leave(self, _e):
        old, self.hover = self.hover, None
        self._recolor(old)

    def _drag(self, e):
        if not self.track_geom:
            return
        ty0, ty1, th = self.track_geom
        ratio = (e.y - ty0 - th / 2) / max(1, (ty1 - ty0) - th)
        first = int(round(max(0.0, min(1.0, ratio)) * max(0, len(self.rows) - self.page)))
        if first != self.first:
            self.first = first
            self.redraw()


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
        self.settings = self.load_settings()
        self.original_size = self.compute_original_size()   # "Reset to original size" returns here
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        w, h = self.original_size
        root.geometry(f"{w}x{h}+{(sw - w) // 2}+{max(0, (sh - h) // 3)}")
        root.minsize(320, 460)
        root.configure(bg=SPLASH_BG)
        try:   # scale pixel sizes on high-DPI screens
            self.sc = max(1.0, min(2.5, root.winfo_fpixels("1i") / 96.0))
        except tk.TclError:
            self.sc = 1.0

        self.player = SoundPlayer(root)
        self.bank = SoundBank()
        self.init_state()
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        # the loading screen goes up first; the real work happens behind it, step by step,
        # so the animation keeps running while the interface is built
        self.splash = Splash(self) if self.settings["show_splash"] else None
        if self.splash:
            root.update()
        self.steps = [   # (message, progress when done, function, minimum ms on screen)
            ("Loading your schedules…", 0.10, self.boot_data, 260),
            ("Tuning alarm sounds…", 0.22, self.boot_sounds, 300),
            ("Setting up the stage…", 0.34, self.boot_ui_a, 160),
            ("Building the schedule form…", 0.46, self.boot_ui_b, 160),
            ("Building the schedule list…", 0.58, self.boot_ui_c, 160),
            ("Wiring up buttons and shortcuts…", 0.70, self.boot_ui_d, 260),
            ("Starting the background…", 0.82, self.boot_media, 280),
            ("Warming up the engine…", 0.93, self.boot_wait, 200),
            ("Almost there…", 1.0, self.boot_finish, 120),
        ]
        self.boot_i, self.boot_started = 0, -1
        self.boot_step_t0 = time.time()
        if self.splash:
            root.after(80, self.boot_next)
        else:
            self.boot_sync()

    def init_state(self):
        self.schedules = []
        self.booting = True
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
        self._saved_geom = None
        self._saved_state = "normal"
        self.mode = None
        self.compact = False
        self.tab = "list"
        self.W = self.H = 1
        self.top = self.px(96)
        self.chip_small = False
        self._cols = None
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
        self.settings_dialog = None
        self.pregen_thread = None
        self.boot_notice = None
        self.boot_wait_t0 = None

    # ------------------------------------------------------------ staged startup
    def boot_next(self):
        if self.boot_i >= len(self.steps):
            return
        msg, prog, fn, min_ms = self.steps[self.boot_i]
        if self.boot_started != self.boot_i:
            self.boot_started, self.boot_step_t0 = self.boot_i, time.time()
            if self.splash:
                self.splash.set_message(msg)
        try:
            done = fn()
        except Exception:
            traceback.print_exc()
            done = True                       # never get stuck on the loading screen
        if not done:
            self.root.after(60, self.boot_next)
            return
        if self.splash:
            self.splash.set_progress(prog)
        self.boot_i += 1
        elapsed = (time.time() - self.boot_step_t0) * 1000
        self.root.after(max(30, int(min_ms - elapsed)), self.boot_next)

    def boot_sync(self):
        """No loading screen: run every step straight away."""
        for _msg, _prog, fn, _ms in self.steps:
            for _ in range(250):
                try:
                    if fn():
                        break
                except Exception:
                    traceback.print_exc()
                    break
                self.root.update()
                time.sleep(0.02)

    def boot_data(self):
        self.schedules = self.load()
        return True

    def boot_sounds(self):
        self.pregen_thread = self.pregenerate()
        return True

    def boot_ui_a(self):
        self.setup_styles()
        self.canvas = tk.Canvas(self.root, bg=BG, highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.bg_item = self.canvas.create_image(0, 0, anchor="nw")
        self.card_rects = [self.canvas.create_rectangle(
            0, 0, 0, 0, fill=CARD, outline="#25376a") for _ in range(2)]   # used when no background
        self.make_stars()
        self.make_header()
        if self.splash:
            self.splash.tkraise()             # keep the loading screen on top
        return True

    def boot_ui_b(self):
        self.build_left()
        return True

    def boot_ui_c(self):
        self.build_right()
        return True

    def boot_ui_d(self):
        small = ("Helvetica", 9, "bold")
        lift = lambda name: (lambda up: self.lift_btn(getattr(self, name), up))
        mk = lambda text, cmd, win: HoverButton(self.canvas, text, cmd, padx=10, pady=5,
                                                font=small, on_hover=lift(win))
        self.nav_list = mk("📋 List", lambda: self.show_tab("list"), "nav_list_win")
        self.nav_new = mk("＋ New", lambda: self.show_tab("form"), "nav_new_win")
        self.scenery_btn = mk("🌌 View scenery", self.toggle_panels, "scenery_win")
        self.sound_btn = mk("🔊 Sound", lambda: self.open_settings("sound"), "sound_win")
        self.bg_btn = mk("🎬 Background", lambda: self.open_settings("background"), "bg_win")
        self.nav_list_win = self.canvas.create_window(0, 0, window=self.nav_list, anchor="nw")
        self.nav_new_win = self.canvas.create_window(0, 0, window=self.nav_new, anchor="nw")
        self.scenery_win = self.canvas.create_window(0, 0, window=self.scenery_btn, anchor="e")
        self.sound_win = self.canvas.create_window(0, 0, window=self.sound_btn, anchor="e")
        self.bg_win = self.canvas.create_window(0, 0, window=self.bg_btn, anchor="e")
        self.build_menu()

        self.canvas.bind("<Configure>", self.on_resize)
        self.bind_keys()
        for seq in ("<Key>", "<ButtonPress>", "<MouseWheel>"):
            self.root.bind_all(seq, lambda e: self.wake_up(), add="+")
        self.root.bind_all("<Motion>", self.on_motion, add="+")
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.root.bind_all(seq, self.on_wheel, add="+")
        self.root.bind("<Unmap>", self.on_unmap)
        self.root.bind("<Map>", self.on_map)
        for item in self.title_items:        # double-click the title: back to the original size
            self.canvas.tag_bind(item, "<Double-Button-1>", lambda e: self.reset_window_size())

        self.reset_form()
        self.set_filter("All")
        self.root.update_idletasks()
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        if cw > 50 and ch > 50:
            self.layout(cw, ch)
        self.tick()
        self.twinkle()
        self.pump_bg()
        return True

    def boot_media(self):
        self.boot_notice = self.start_background()
        return True

    def boot_wait(self):
        """Wait (briefly) for the alarm sounds and the first video frame to be ready."""
        if self.boot_wait_t0 is None:
            self.boot_wait_t0 = time.time()
        timed_out = time.time() - self.boot_wait_t0 > 3.5
        sounds_ready = self.pregen_thread is None or not self.pregen_thread.is_alive()
        frame_ready = self.engine is None or self.engine.frames > 0
        return timed_out or (sounds_ready and frame_ready)

    def boot_finish(self):
        self.booting = False
        if self.boot_notice:
            self.root.after(2200, lambda: self.toast(self.boot_notice))
        if self.splash:
            self.splash.finish(on_reveal=self.reveal, on_done=self.splash_gone)
        else:
            self.reveal()
        return True

    def reveal(self):
        """The curtain starts to lift: let the panels glide in underneath it."""
        self.last_input = time.time()
        self.start_intro()

    def splash_gone(self):
        self.splash = None

    # ------------------------------------------------------------ helpers
    def px(self, n):
        return int(n * self.sc)

    def on_close(self):
        self.player.stop()
        self.stop_background()
        self.root.destroy()

    # ---- window size (the "original size" is a setting)
    def auto_size(self):
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        return min(1120, int(sw * 0.92)), min(720, int(sh * 0.88))

    def clamp_size(self, w, h):
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        return max(320, min(int(w), sw)), max(460, min(int(h), sh))

    def compute_original_size(self):
        w, h = self.settings["win_w"], self.settings["win_h"]
        return self.clamp_size(w, h) if w > 0 and h > 0 else self.auto_size()

    def resize_window(self, w, h):
        """Put the window at w x h, centred (also leaves fullscreen / maximised)."""
        if self.fullscreen:
            self.fullscreen = False
            self.root.attributes("-fullscreen", False)
        try:
            self.root.state("normal")
        except tk.TclError:
            pass
        w, h = self.clamp_size(w, h)
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry(f"{w}x{h}+{(sw - w) // 2}+{max(0, (sh - h) // 3)}")

    def reset_window_size(self):
        """Back to the original size from Settings -> Window."""
        self.resize_window(*self.original_size)
        self.toast("Window reset to its original size")

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
                st.update({k: v for k, v in json.load(f).items() if k in DEFAULT_SETTINGS})
        except (FileNotFoundError, json.JSONDecodeError):
            pass
        if st["alarm_sound"] not in ALL_SOUNDS:
            st["alarm_sound"] = DEFAULT_SETTINGS["alarm_sound"]
        if st["reminder_sound"] not in ALL_SOUNDS:
            st["reminder_sound"] = DEFAULT_SETTINGS["reminder_sound"]
        for key, lo, hi in (("volume", 20, 100), ("ring_seconds", 0, 3600),
                            ("snooze_min", 1, 120), ("bg_fps", 5, 60),
                            ("idle_hide", 0, 3600), ("panel_opacity", 20, 100),
                            ("win_w", 0, 8000), ("win_h", 0, 8000)):
            try:   # each value is checked on its own, so one bad entry can't reset the rest
                st[key] = max(lo, min(hi, int(st[key])))
            except (TypeError, ValueError):
                st[key] = DEFAULT_SETTINGS[key]
        st["bg_play"] = bool(st["bg_play"])
        st["show_splash"] = bool(st["show_splash"])

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
        for path in self.background_candidates():
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
            self.engine.set_glass(self.settings["panel_opacity"])
            self.bg_path = path
            break
        if self.engine is None and notice is None:
            notice = "No background found — put background.mp4 next to this file"
        self.set_stars_visible(self.engine is None or self.engine.source.static)
        if self.W > 1:
            self.push_view()
            self.apply_visibility()
        return notice

    def background_candidates(self):
        """Files to try, best first: your choice, then a video, then a picture."""
        pref = self.settings.get("background", "")
        video, image = find_media(BASE_DIR)
        return ([pref] if pref and os.path.exists(pref) else []) + [video, image]

    def first_background_path(self):
        """The first background file that can actually be used (for the loading screen)."""
        for path in self.background_candidates():
            ext = os.path.splitext(path)[1].lower() if path else ""
            if (ext in VIDEO_EXT and HAS_CV2) or ext in IMAGE_EXT:
                return path
        return ""

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
            self.engine.set_glass(self.settings["panel_opacity"])

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

        t = threading.Thread(target=work, daemon=True)
        t.start()
        return t

    def start_sound(self, s, kind):
        """Called by a new popup. Returns the ring length in seconds (None = until stopped)."""
        if kind == "reminder":
            if any(p.alive and p.loud for p in self.popups):
                return None   # don't interrupt a ringing alarm
            path = self.sound_path(self.settings["reminder_sound"])
            self.player.play(path, loop=False, seconds=4)
            return None
        name = self.resolve_sound(s.get("sound"), "due")
        secs = self.settings["ring_seconds"] or None
        self.player.play(self.sound_path(name), loop=True, seconds=secs)
        return secs

    def popup_closed(self):
        if not any(p.alive and p.loud for p in self.popups):
            self.player.stop()

    def open_settings(self, tab="sound"):
        d = self.settings_dialog
        if d is not None and d.winfo_exists():       # already open: just switch tab
            d.show_tab(tab)
            d.tkraise()
            d.focus_set()
            return
        self.settings_dialog = SettingsDialog(self, tab)

    def preview_form_sound(self):
        self.preview(self.sound_var.get(), loop=True, seconds=4)

    # ------------------------------------------------------------ styling
    def setup_styles(self):
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
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

        self.title_items = pair("✦ Schedule Planner", ("Helvetica", 24, "bold"), "w", "#ffffff")
        self.sub_items = pair("Plan it. Get reminded. Never miss a moment.",
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

        self.set_pair(self.title_items, "✦ Planner" if mode == "tiny" else "✦ Schedule Planner")
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


        # --- header texts + buttons
        if self.compact:
            self.put_pair(self.title_items, m + 2, px(24))
            self.put_pair(self.clock_items, W - m, px(24))
            self.put_pair(self.date_items, W - m, px(46))
            n, gap = 5, px(6)
            bw = (W - 2 * m - (n - 1) * gap) // n
            icons = bw < px(130)
            sc_text = self.scenery_text(True)
            slots = [(self.nav_list_win, self.nav_list, "📋 List", "📋"),
                     (self.nav_new_win, self.nav_new, "＋ New", "＋"),
                     (self.scenery_win, self.scenery_btn, sc_text, sc_text.split()[0]),
                     (self.sound_win, self.sound_btn, "🔊 Sound", "🔊"),
                     (self.bg_win, self.bg_btn, "🎬 Background", "🎬")]
            for i, (win, btn, full, icon) in enumerate(slots):
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
            est = lambda t: int(len(t) * 7.4 * self.sc) + px(30)
            x = W - m - px(190)                # buttons line up leftwards from the clock
            for win, btn, text in ((self.scenery_win, self.scenery_btn, self.scenery_text(False)),
                                   (self.sound_win, self.sound_btn, "🔊 Sound"),
                                   (self.bg_win, self.bg_btn, "🎬 Background")):
                btn.configure(text=text)
                c.itemconfigure(win, anchor="e", width="", height="", state="normal")
                self.put_win(win, x, px(52))
                x -= est(text) + px(8)
        self.put_pair(self.next_items, m + 2, H - px(20))
        self.place_stars(W, H)

        # keep the panels where they belong (unless an animation is moving them)
        if self.intro_wait:
            self.panel_shift = self.hide_distance()
        elif self.anim_job is None:
            self.panel_shift = 0 if self.show_panels else self.hide_distance()
        self.adapt_right(self.right_box[2] - self.right_box[0])
        self.apply_visibility()
        self.place_panels()

    def place_panels(self):
        """Position everything on the panels (including the slide offset) and the glass behind."""
        c, sh = self.canvas, self.panel_shift
        for rect, box in zip(self.card_rects, (self.left_box, self.right_box)):
            c.coords(rect, box[0], box[1] + sh, box[2], box[3] + sh)
        self.form.set_geometry(self.left_box, sh)
        self.layout_right()
        self.push_view()

    def layout_right(self):
        """Filter chips, search, schedule cards, details and action buttons on the right panel."""
        px, c, sh = self.px, self.canvas, self.panel_shift
        x0, y0, x1, y1 = self.right_box
        pad = px(14)
        ix, iw = x0 + pad, x1 - x0 - 2 * pad
        y = y0 + pad + sh
        ch = px(30)                                         # filter chips (wrap if they don't fit)
        for line in self.flow_rows([(self.chips[n], self.chip_wins[n]) for n in FILTERS], iw, px(5)):
            x = ix
            for btn, wid, wn in line:
                c.coords(wid, x, y)
                c.itemconfigure(wid, width=wn, height=ch)
                x += wn + px(5)
            y += ch + px(5)
        y += px(5)
        sh_h = px(30)                                        # search box
        self.search_icon.place(ix + px(2), y + (sh_h - self.search_icon.size()[1]) // 2)
        c.coords(self.search_win, ix + px(24), y)
        c.itemconfigure(self.search_win, width=max(px(40), iw - px(24)), height=sh_h)
        y += sh_h + px(10)

        bottom = y1 - pad + sh                               # bottom stack, built upwards
        if not self.compact:
            hint_h = px(14)
            self.hint.place(ix, bottom - hint_h)
            bottom -= hint_h + px(8)
        ah = px(34)                                          # action buttons (wrap if needed)
        for line in reversed(self.flow_rows(list(zip(self.action_btns, self.action_wins)), iw, px(5))):
            x = ix
            for btn, wid, wn in line:
                c.coords(wid, x, bottom - ah)
                c.itemconfigure(wid, width=wn, height=ah)
                x += wn + px(5)
            bottom -= ah + px(5)
        bottom -= px(3)
        dh = px(50)
        self.detail.configure(wraplength=iw)
        self.detail.place(ix, bottom - dh)
        bottom -= dh + px(8)
        self.tree.set_geometry((ix, y - sh, ix + iw, bottom - sh), self.list_cols, sh)

    @staticmethod
    def flow_rows(pairs, width, gap):
        """Split (widget, window-id) pairs into lines that fit in `width` -> [[(w, id, w_px)]]."""
        lines, cur, x = [], [], 0
        for btn, wid in pairs:
            wn = btn.winfo_reqwidth()
            if cur and x + wn > width:
                lines.append(cur)
                cur, x = [], 0
            cur.append((btn, wid, wn))
            x += wn + gap
        if cur:
            lines.append(cur)
        return lines

    def apply_visibility(self):
        c = self.canvas
        active = self.panels_active()
        show_form = active and (not self.compact or self.tab == "form")
        show_list = active and (not self.compact or self.tab == "list")
        self.form.set_visible(show_form)
        state = "normal" if show_list else "hidden"
        for i in self.right_ids:
            c.itemconfigure(i, state=state)
        self.hint.show(show_list and not self.compact)
        self.tree.set_visible(show_list)
        no_bg = self.engine is None
        for rect, show in zip(self.card_rects, (show_form, show_list)):
            c.itemconfigure(rect, state="normal" if (show and no_bg) else "hidden")
        self.nav_list.set_base(ACCENT if self.tab == "list" else BTN)
        self.nav_new.set_base(ACCENT if self.tab == "form" else BTN)
        for win in (self.nav_list_win, self.nav_new_win):
            c.itemconfigure(win, state="normal" if self.compact else "hidden")

    def adapt_right(self, cardw):
        """Show fewer list columns / smaller chips when the list panel is narrow."""
        px = self.px
        self.list_cols = (self.COLS_WIDE if cardw >= px(600) else
                          self.COLS_MEDIUM if cardw >= px(420) else self.COLS_NARROW)
        small = cardw < px(440)
        if small != self.chip_small:
            self.chip_small = small
            self.update_chips(relayout=False)
            for b in self.action_btns:
                b.configure(padx=px(8) if small else px(14))

    def on_wheel(self, e):
        """Mouse wheel over the form or the schedule list scrolls it."""
        try:
            w = self.root.winfo_containing(e.x_root, e.y_root)
            if w is None or w.winfo_toplevel() is not self.root:
                return
            x = e.x_root - self.canvas.winfo_rootx()
            y = e.y_root - self.canvas.winfo_rooty()
        except (tk.TclError, KeyError):
            return
        step = -1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1
        sh = self.panel_shift
        inside = lambda b: b[0] <= x <= b[2] and b[1] + sh <= y <= b[3] + sh
        if self.form.visible and inside(self.left_box):
            self.form.scroll_by(step)
        elif self.tree.visible and inside(self.right_box):
            self.tree.scroll_by(step)

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
        if (not secs or self.booting or not self.show_panels or self.engine is None or self.popups
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
        """F11.  Remembers the window size / state so leaving fullscreen puts it back."""
        if not self.fullscreen:
            self._saved_geom = self.root.geometry()
            try:
                self._saved_state = self.root.state()
            except tk.TclError:
                self._saved_state = "normal"
            self.fullscreen = True
            self.root.attributes("-fullscreen", True)
        else:
            self.fullscreen = False
            self.root.attributes("-fullscreen", False)
            self.root.after(120, self._restore_after_fullscreen)

    def _restore_after_fullscreen(self):
        try:
            if self._saved_state == "zoomed":
                self.root.state("zoomed")
            else:
                self.root.state("normal")
                if self._saved_geom:
                    self.root.geometry(self._saved_geom)
        except tk.TclError:
            pass

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
        c, px = self.canvas, self.px
        self.form = F = FormView(self)
        self.title_var = tk.StringVar()
        self.date_var = tk.StringVar()
        self.hour_var = tk.StringVar()
        self.min_var = tk.StringVar()
        self.remind_var = tk.StringVar()
        self.sound_var = tk.StringVar(value="Default")

        def label(text):
            F.row(px(20), [F.t(CText(c, text.upper(), size=8, bold=True, fill=MUTED))], top=px(8))

        self.form_title = CText(c, "＋ New schedule", size=14, bold=True, fill="#ffffff")
        F.row(px(34), [F.t(self.form_title)])

        label("Title")
        self.title_entry = self.entry(c, self.title_var)
        F.row(px(34), [F.w(self.title_entry, "fill", px(34))])

        label("Date  (YYYY-MM-DD)")
        self.date_entry = self.entry(c, self.date_var, width=12)
        F.row(px(34), [F.w(self.date_entry, "fill", px(34)),
                       F.w(HoverButton(c, "📅", self.open_calendar, padx=9, pady=4)),
                       F.w(HoverButton(c, "Today", self.set_today, padx=10, pady=4,
                                       font=("Helvetica", 9, "bold")))])

        label("Time  (24-hour)")
        self.hour_spin = self.spin(c, self.hour_var, 23)
        self.min_spin = self.spin(c, self.min_var, 59)
        F.row(px(34), [F.w(self.hour_spin, px(64), px(34)),
                       F.t(CText(c, ":", size=14, bold=True, fill=TEXT)),
                       F.w(self.min_spin, px(64), px(34))], gap=px(4))
        small = ("Helvetica", 8, "bold")
        F.row(px(30), [
            F.w(HoverButton(c, "+30 min", lambda: self.quick(timedelta(minutes=30)),
                            padx=8, pady=3, font=small)),
            F.w(HoverButton(c, "+1 hour", lambda: self.quick(timedelta(hours=1)),
                            padx=8, pady=3, font=small)),
            F.w(HoverButton(c, "Tomorrow 9:00", lambda: self.quick(None),
                            padx=8, pady=3, font=small))], top=px(8), gap=px(5))

        label("Remind me before")
        remind = ttk.Combobox(c, textvariable=self.remind_var, width=6,
                              values=["0", "5", "10", "15", "30", "60", "120", "1440"])
        F.row(px(34), [F.w(remind, px(76), px(30)),
                       F.t(CText(c, "minutes  (0 = none)", size=9, fill=MUTED))], gap=px(8))

        label("Alarm sound")
        sound = ttk.Combobox(c, textvariable=self.sound_var, state="readonly", width=17,
                             values=["Default"] + ALL_SOUNDS)
        F.row(px(34), [F.w(sound, "fill", px(30)),
                       F.w(HoverButton(c, "▶", self.preview_form_sound, padx=9, pady=4)),
                       F.w(HoverButton(c, "■", self.player.stop, padx=9, pady=4))])

        label("Notes")
        self.notes_text = tk.Text(c, height=3, wrap="word", bg=INPUT, fg=TEXT,
                                  insertbackground=TEXT, relief="flat", padx=8, pady=6,
                                  font=("Helvetica", 10), highlightthickness=1,
                                  highlightbackground=EDGE, highlightcolor=ACCENT)
        F.row(px(72), [F.w(self.notes_text, "fill", px(72))])

        self.save_btn = HoverButton(c, "Add schedule", self.save_schedule, bg=ACCENT,
                                    pady=9, pulse=True)   # the glow "breathes" to invite a click
        F.row(px(44), [F.w(self.save_btn, "fill", px(40)),
                       F.w(HoverButton(c, "Clear", self.reset_form, pady=9), "nat", px(40))],
              top=px(14))

    def build_right(self):
        c, px = self.canvas, self.px
        self.right_ids = []
        self.chips, self.chip_wins = {}, {}
        for name in FILTERS:
            b = HoverButton(c, name, lambda n=name: self.set_filter(n), padx=11, pady=5,
                            font=("Helvetica", 9, "bold"))
            wid = c.create_window(0, 0, window=b, anchor="nw", state="hidden")
            self.chips[name], self.chip_wins[name] = b, wid
            self.right_ids.append(wid)

        self.search_icon = CText(c, "🔍", size=10, fill=MUTED)
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self.refresh_table())
        self.search_entry = self.entry(c, self.search_var, 10)
        self.search_win = c.create_window(0, 0, window=self.search_entry, anchor="nw", state="hidden")
        self.right_ids += self.search_icon.ids + [self.search_win]

        self.tree = ScheduleList(self)          # same small API the old table had
        self.list_cols = self.COLS_WIDE

        self.detail = CText(c, "", size=10, fill=MUTED)
        self.right_ids += self.detail.ids
        self.action_btns = [
            HoverButton(c, "Edit", self.edit_selected),
            HoverButton(c, "Done / Undo", self.toggle_done),
            HoverButton(c, "Duplicate", self.duplicate_selected),
            HoverButton(c, "Delete", self.delete_selected, bg=DANGER),
        ]
        self.action_wins = []
        for b in self.action_btns:
            wid = c.create_window(0, 0, window=b, anchor="nw", state="hidden")
            self.action_wins.append(wid)
            self.right_ids.append(wid)
        self.hint = CText(c, "Double-click to edit  ·  Right-click for options  ·  Del to delete",
                          size=8, fill=FAINT)

    def build_menu(self):
        self.menu = tk.Menu(self.root, tearoff=0, bg=CARD, fg=TEXT, bd=0,
                            activebackground=ACCENT, activeforeground="#ffffff",
                            font=("Helvetica", 10))

    def bind_keys(self):
        r = self.root
        r.bind("<Delete>", lambda e: self.key_action(self.delete_selected))
        r.bind("<Up>", lambda e: self.key_action(lambda: self.tree.move(-1)))
        r.bind("<Down>", lambda e: self.key_action(lambda: self.tree.move(1)))
        r.bind("<Control-n>", lambda e: (self.reset_form(), self.show_tab("form"),
                                         self.title_entry.focus_set()))
        r.bind("<Control-f>", lambda e: (self.show_tab("list"), self.search_entry.focus_set()))
        r.bind("<F11>", lambda e: self.toggle_fullscreen())
        r.bind("<Control-Key-0>", lambda e: self.reset_window_size())
        r.bind("<Escape>", self.on_escape)
        for w in (self.title_entry, self.date_entry):
            w.bind("<Return>", lambda e: self.save_schedule())

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

    def row_menu(self, iid, xr, yr):
        """Right-click menu for a schedule card."""
        s = self.by_id(iid)
        if s is None:
            return
        self.menu.delete(0, "end")
        self.menu.add_command(label="Edit", command=self.edit_selected)
        self.menu.add_command(label="Mark as not done" if s["done"] else "Mark as done",
                              command=self.toggle_done)
        self.menu.add_command(label="Duplicate to next day", command=self.duplicate_selected)
        self.menu.add_separator()
        self.menu.add_command(label="Delete", command=self.delete_selected)
        try:
            self.menu.tk_popup(xr, yr)
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

    def update_chips(self, relayout=True):
        small = self.chip_small
        for name, b in self.chips.items():
            n = self.counts[name]
            b.configure(text=name if (small or not n) else f"{name}  {n}",
                        padx=self.px(5) if small else self.px(11),
                        font=("Helvetica", 8 if small else 9, "bold"))
        if relayout and self.W > 1:
            self.layout_right()

    def refresh_table(self):
        """Rebuild the schedule cards - only runs when something actually changed (no flicker)."""
        now = datetime.now()
        query = self.search_var.get().strip().lower()
        statuses, counts, rows = {}, dict.fromkeys(FILTERS, 0), []

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
            rows.append({
                "iid": s["id"], "status": st,
                "tag": {"Overdue": "overdue", "Due soon": "soon", "Done": "done"}.get(st, ""),
                "vals": {"date": dt.strftime("%b %d, %Y"), "time": dt.strftime("%H:%M"),
                         "when": dt.strftime("%b %d · %H:%M"), "title": s["title"],
                         "left": self.countdown(s, now), "status": st}})

        self.status_cache = statuses
        self.counts = counts
        self.tree.set_rows(rows)
        self.update_chips()
        self.show_details()

    def show_details(self):
        s = self.selected(quiet=True)
        if not s:
            self.detail.configure(text="Select a schedule to see its details.")
            return
        dt = self.when(s)
        iw = max(160, self.right_box[2] - self.right_box[0] - 2 * self.px(14))
        chars = max(16, int(iw / (6.3 * self.sc)))
        cut_to = lambda t: t if len(t) <= chars else t[:chars - 1] + "…"
        remind = f"⏰ {s['remind']} min before" if s["remind"] else "no reminder"
        when = dt.strftime("%a, %b %d · %H:%M") if iw < self.px(520) else dt.strftime("%A, %B %d, %Y at %H:%M")
        sound = self.resolve_sound(s.get("sound"), "due")
        notes = s["notes"].replace("\n", " ") or "No notes"
        self.detail.configure(text=f"{cut_to(s['title'])}\n"
                                   f"{cut_to(f'{when}  ·  {remind}  ·  🔊 {sound}')}\n{cut_to(notes)}")

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