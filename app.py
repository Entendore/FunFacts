#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Shorts Studio v2.3 — text Shorts (1080x1920 MP4) from text slides, images + music.

Install:
    pip install PySide6 Pillow moviepy
Optional:
    pip install pilmoji        # emoji support in exported text
Run:
    python shorts_studio.py

Drag & drop onto the window:
    image  -> background of the selected slide
    .txt   -> split-into-slides import
    audio  -> background music
"""

from __future__ import annotations

import copy
import json
import os
import random
import re
import sys
import tempfile
import uuid
from dataclasses import dataclass, asdict, fields

from PySide6.QtCore import (Qt, QRect, QSize, QTimer, QThread, QUrl,
                            QSettings, Signal)
from PySide6.QtGui import (QColor, QDesktopServices, QFont, QKeySequence,
                           QImage, QPainter, QPixmap, QPen, QShortcut, QIcon)
from PySide6.QtWidgets import (
    QApplication, QAbstractSpinBox, QCheckBox, QColorDialog, QComboBox,
    QDialog, QDoubleSpinBox, QFileDialog, QFontComboBox, QFormLayout, QFrame,
    QGroupBox, QHBoxLayout, QLabel, QLineEdit, QListWidget, QListWidgetItem,
    QMainWindow, QMessageBox, QPlainTextEdit, QProgressBar, QPushButton,
    QScrollArea, QSlider, QSplitter, QTabWidget, QVBoxLayout, QWidget,
)

from PIL import Image, ImageDraw, ImageFont, ImageFilter

# ------------------------------------------------------------- optional libs
try:
    from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
    MEDIA_OK = True
except Exception:
    MEDIA_OK = False

try:
    import moviepy
    try:                                    # moviepy >= 2.0
        from moviepy import (AudioFileClip, CompositeAudioClip, ImageClip,
                             VideoClip, concatenate_audioclips,
                             concatenate_videoclips)
    except ImportError:                     # moviepy 1.x
        from moviepy.editor import (AudioFileClip, CompositeAudioClip,
                                    ImageClip, VideoClip,
                                    concatenate_audioclips,
                                    concatenate_videoclips)
    MOVIEPY_OK = True
except Exception:
    MOVIEPY_OK = False

try:
    from pilmoji import Pilmoji
    PILMOJI_OK = True
except Exception:
    PILMOJI_OK = False

# -------------------------------------------------------------------- config
BASE_W, BASE_H = 1080, 1920               # reference size for style values
SHORTS_LIMIT_S = 180                      # YouTube Shorts max: 3 minutes
APP_NAME, APP_VERSION = "Shorts Studio", "2.3"
PREVIEW_SIZE = (540, 960)
THUMB_SIZE = (48, 86)                     # slide-list thumbnail
THUMB_RENDER = (216, 384)                 # rendered then scaled down
RECOVERY_PATH = os.path.join(tempfile.gettempdir(),
                             "shorts_studio_recovery.json")
IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".bmp")
AUD_EXTS = (".mp3", ".wav", ".m4a", ".aac", ".ogg", ".flac")

ANIMS = ["none", "fade", "slide-up", "typewriter", "pop"]
ANIM_LABELS = ["None", "Fade in", "Slide up", "Typewriter", "Pop"]

PALETTES = [
    ("#0f172a", "#2563eb", "#ffffff"),
    ("#1e1b4b", "#ec4899", "#ffffff"),
    ("#052e16", "#16a34a", "#ffffff"),
    ("#450a0a", "#f97316", "#ffffff"),
    ("#111827", "#6b7280", "#f9fafb"),
    ("#fff7ed", "#fb923c", "#1f2937"),
    ("#f0fdfa", "#14b8a6", "#134e4a"),
]

DEFAULT_SLIDES = [
    ("Wild facts you can use\nto impress anyone 👇", 4.0),
    ("1. Honey never spoils.\n3,000-year-old honey from\nEgyptian tombs is still edible 🍯", 6.0),
    ("2. Octopuses have\nthree hearts\nand blue blood 🐙", 4.5),
    ("3. A day on Venus\nlasts longer than\nits entire year 🪐", 5.5),
    ("4. Sharks are older\nthan trees —\nby about 50 million years 🦈", 6.0),
    ("5. Wombats are the only\nanimals that poop\ncube-shaped blocks 🟫", 5.0),
    ("Which fact was\nyour favorite?\nFollow for more!", 4.0),
]


@dataclass
class Slide:
    text: str = ""
    duration: float = 4.0
    anim: str = "fade"
    bg_image: str = ""
    trans: float = 0.0       # crossfade from previous slide, seconds
    color: str = ""          # per-slide text color, "" = inherit style
    size: int = 0            # per-slide font size px, 0 = inherit style
    uid: str = ""

    def __post_init__(self):
        if not self.uid:
            self.uid = uuid.uuid4().hex


@dataclass
class Style:
    font_family: str = "Arial"
    bold: bool = False             # prefer the family's bold font file
    font_size: int = 84            # px at 1080-wide reference
    text_color: str = "#ffffff"
    outline: bool = True
    outline_color: str = "#000000"
    outline_width: int = 5
    shadow: bool = False
    bg1: str = "#0f172a"
    bg2: str = "#06b6d4"
    gradient: bool = True
    align: str = "center"
    vpos: str = "middle"
    fit: bool = True
    dim: int = 0                   # darken background, %
    backdrop: bool = False         # rounded pill behind the text
    backdrop_color: str = "#000000"
    backdrop_alpha: int = 110
    kenburns: bool = True
    progress_bar: bool = False
    watermark_on: bool = False
    watermark_text: str = "@yourhandle"
    emoji: bool = True            # enabled by default for the new fun facts
    fades: bool = True


@dataclass
class RenderOpts:
    size: tuple = PREVIEW_SIZE
    progress_bar: bool = False
    watermark: str = ""
    emoji: bool = False
    kenburns: bool = True


def read_speed(text: str) -> float:
    """Estimated seconds needed to read the text (≈2.5 words/s)."""
    words = len(text.split())
    return round(min(60.0, max(1.2, words / 2.5 + 0.6)), 1)


def split_sentences(text: str) -> list:
    parts = re.split(r"(?<=[.!?])\s+", text.replace("\n", " "))
    return [p.strip() for p in parts if p.strip()]


# --------------------------------------------------------- font machinery ---
_FONT_FILE_CACHE: dict = {}
_BOLD_FILE_CACHE: dict = {}
_FONT_OBJ_CACHE: dict = {}


def _clean(name: str) -> str:
    for ch in " -_":
        name = name.replace(ch, "")
    return name.lower()


def _font_roots() -> list:
    if sys.platform.startswith("win"):
        return [os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts")]
    if sys.platform == "darwin":
        return ["/System/Library/Fonts", "/Library/Fonts",
                os.path.expanduser("~/Library/Fonts")]
    return ["/usr/share/fonts", "/usr/local/share/fonts",
            os.path.expanduser("~/.fonts"),
            os.path.expanduser("~/.local/share/fonts")]


def _find_font_file(family: str):
    if family in _FONT_FILE_CACHE:
        return _FONT_FILE_CACHE[family]
    target = _clean(family)
    exact = partial = None
    for root in _font_roots():
        if not os.path.isdir(root):
            continue
        for dirpath, _d, files in os.walk(root):
            for f in files:
                if not f.lower().endswith((".ttf", ".otf", ".ttc")):
                    continue
                stem = _clean(os.path.splitext(f)[0])
                if stem == target:
                    exact = os.path.join(dirpath, f)
                    break
                if partial is None and target in stem:
                    partial = os.path.join(dirpath, f)
            if exact:
                break
        if exact:
            break
    path = exact or partial
    _FONT_FILE_CACHE[family] = path
    return path


def _find_bold_font_file(family: str):
    """Locate a bold variant: arialbd.ttf, 'Arial Bold.ttf', DejaVuSans-Bold…"""
    if family in _BOLD_FILE_CACHE:
        return _BOLD_FILE_CACHE[family]
    target = _clean(family)

    def score(stem: str):
        if stem == target + "bold":
            return 0
        if "bold" in stem:
            return 1
        if stem.endswith("bd"):
            return 2
        return 9

    best = None
    for root in _font_roots():
        if not os.path.isdir(root):
            continue
        for dirpath, _d, files in os.walk(root):
            for f in files:
                if not f.lower().endswith((".ttf", ".otf", ".ttc")):
                    continue
                stem = _clean(os.path.splitext(f)[0])
                if target in stem:
                    sc = score(stem)
                    if sc < 9 and (best is None or sc < best[0]
                                   or (sc == best[0] and len(stem) < len(best[2]))):
                        best = (sc, os.path.join(dirpath, f), stem)
            if best and best[0] == 0:
                break
        if best and best[0] == 0:
            break
    path = best[1] if best else None
    _BOLD_FILE_CACHE[family] = path
    return path


def _load_font(family: str, size: int, bold: bool = False):
    key = (family, size, bold)
    if key in _FONT_OBJ_CACHE:
        return _FONT_OBJ_CACHE[key]
    font = None
    if bold:
        bpath = _find_bold_font_file(family)
        if bpath:
            try:
                font = ImageFont.truetype(bpath, size)
            except Exception:
                font = None
    if font is None:
        path = _find_font_file(family)
        if path:
            try:
                font = ImageFont.truetype(path, size)
            except Exception:
                font = None
    if font is None:
        for cand in ("DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf",
                     "Arial.ttf", "arial.ttf"):
            try:
                font = ImageFont.truetype(cand, size)
                break
            except Exception:
                continue
    if font is None:
        for fam in ("DejaVu Sans", "Liberation Sans", "Segoe UI",
                    "Roboto", "Helvetica"):
            p = _find_bold_font_file(fam) if bold else _find_font_file(fam)
            p = p or _find_font_file(fam)
            if p:
                try:
                    font = ImageFont.truetype(p, size)
                    break
                except Exception:
                    continue
    if font is None:
        try:
            font = ImageFont.load_default(size)
        except TypeError:
            font = ImageFont.load_default()
    _FONT_OBJ_CACHE[key] = font
    return font


def _text_width(font, s: str) -> float:
    try:
        return font.getlength(s)
    except AttributeError:
        return font.getsize(s)[0]


def _line_height(font) -> int:
    try:
        asc, desc = font.getmetrics()
        return max(1, int((asc + desc) * 1.22))
    except Exception:
        return int(_text_width(font, "Ag") * 2.2)


def _wrap(text: str, font, max_w: float) -> list:
    lines = []
    for para in text.split("\n"):
        words = para.split()
        if not words:
            lines.append("")
            continue
        cur = words[0]
        for w in words[1:]:
            trial = f"{cur} {w}"
            if _text_width(font, trial) <= max_w:
                cur = trial
            else:
                lines.append(cur)
                cur = w
        lines.append(cur)
    return lines


def _hex_rgba(hex_color: str, alpha=255):
    c = QColor(hex_color)
    return (c.red(), c.green(), c.blue(), alpha)


def _cover(img: Image.Image, w: int, h: int) -> Image.Image:
    scale = max(w / img.width, h / img.height)
    nw = max(w, int(img.width * scale + 0.5))
    nh = max(h, int(img.height * scale + 0.5))
    img = img.resize((nw, nh), Image.LANCZOS)
    x, y = (nw - w) // 2, (nh - h) // 2
    return img.crop((x, y, x + w, y + h))


def _ease(u: float) -> float:
    u = max(0.0, min(1.0, u))
    return u * u * (3 - 2 * u)


def _ease_back(u: float) -> float:
    u = max(0.0, min(1.0, u))
    c1, c3 = 1.70158, 2.70158
    return 1 + c3 * (u - 1) ** 3 + c1 * (u - 1) ** 2


def _draw_text_on(draw_or_img, xy, line, font, fill, stroke, stroke_fill,
                  emoji: bool):
    if emoji and PILMOJI_OK:
        try:
            with Pilmoji(draw_or_img) as pj:
                pj.text(xy, line, font=font, fill=fill,
                        stroke_width=stroke, stroke_fill=stroke_fill)
            return
        except TypeError:
            try:
                with Pilmoji(draw_or_img) as pj:
                    pj.text(xy, line, font=font, fill=fill)
                return
            except Exception:
                pass
        except Exception:
            pass
    draw_or_img.text(xy, line, font=font, fill=fill,
                     stroke_width=stroke, stroke_fill=stroke_fill)


# ------------------------------------------------------------- SlideRenderer
class SlideRenderer:
    """One slide at any size/time: animation, Ken Burns, crossfade-in,
    dim overlay, backdrop pill, watermark, progress bars."""

    ZB = 1.08

    def __init__(self, slide: Slide, style: Style, opts: RenderOpts,
                 prev_frame: Image.Image | None = None):
        self.slide, self.style, self.opts = slide, style, opts
        self.W, self.H = opts.size
        self.dur = max(0.1, slide.duration)
        self.anim = slide.anim if slide.anim in ANIMS else "none"
        self.prev = prev_frame
        self.trans = (min(max(0.0, slide.trans), self.dur * 0.8)
                      if prev_frame is not None else 0.0)
        self.fill = slide.color or style.text_color      # effective color
        self.bold = style.bold

        # background ---------------------------------------------------------
        has_img = bool(slide.bg_image) and os.path.exists(slide.bg_image)
        self.zoom = self.ZB if (has_img and opts.kenburns) else 1.0
        if has_img:
            try:
                src = Image.open(slide.bg_image)
                
                # Performance Optimization: Pre-scale massive images down 
                # to roughly 2x the target resolution before cropping/zooming 
                # to drastically save RAM and CPU cycles.
                max_dim = max(self.W, self.H) * 2
                if src.width > max_dim or src.height > max_dim:
                    ratio = max_dim / max(src.width, src.height)
                    src = src.resize((int(src.width * ratio), int(src.height * ratio)), Image.LANCZOS)
                
                src = src.convert("RGB")
                
                if self.zoom > 1.0:
                    self.bg = _cover(src, int(self.W * self.ZB),
                                     int(self.H * self.ZB)).convert("RGBA")
                else:
                    self.bg = _cover(src, self.W, self.H).convert("RGBA")
            except Exception:
                has_img = False
        if not has_img:
            self.bg = self._gradient_bg()
        if self.style.dim > 0:
            ov = Image.new("RGBA", self.bg.size,
                           (0, 0, 0, int(255 * self.style.dim / 100)))
            self.bg.alpha_composite(ov)

        self._layout_text()
        self.wm = self._watermark_layer() if opts.watermark else None

        n = max(1, len(self.layers))
        self.stag = (min(0.18, max(0.04, (self.dur - 0.5) / n))
                     if self.anim == "typewriter" else
                     min(0.15, max(0.03, (self.dur - 0.4) / n)))
        self.anim_t = min(0.6, self.dur * 0.4)

    # ------------------------------------------------------------ pieces ----
    def _gradient_bg(self) -> Image.Image:
        s = self.style
        c1 = QColor(s.bg1)
        img = Image.new("RGBA", (self.W, self.H),
                        (c1.red(), c1.green(), c1.blue(), 255))
        if not s.gradient or s.bg1.lower() == s.bg2.lower():
            return img
        c2 = QColor(s.bg2)
        bot = Image.new("RGBA", (self.W, self.H),
                        (c2.red(), c2.green(), c2.blue(), 255))
        mask = Image.linear_gradient("L").resize((self.W, self.H))
        return Image.composite(bot, img, mask)

    def _line_rgba(self, text, font, lw_ratio, fill_hex=None):
        s = self.style
        stroke = int(s.outline_width * lw_ratio) if s.outline else 0
        fill = _hex_rgba(fill_hex or s.text_color)
        sfill = _hex_rgba(s.outline_color)
        dummy = ImageDraw.Draw(Image.new("RGBA", (1, 1)))
        try:
            bb = dummy.textbbox((0, 0), text, font=font, stroke_width=stroke)
        except Exception:
            bb = (0, 0, int(_text_width(font, text)), font.size)
        pad = stroke + (16 if s.shadow else 2) + 2
        w, h = bb[2] - bb[0], bb[3] - bb[1]
        img = Image.new("RGBA", (max(1, w + 2 * pad), max(1, h + 2 * pad)),
                        (0, 0, 0, 0))
        origin = (pad - bb[0], pad - bb[1])
        if s.shadow:
            sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
            _draw_text_on(ImageDraw.Draw(sh), origin, text, font,
                          (0, 0, 0, 180), stroke, (0, 0, 0, 180),
                          self.opts.emoji)
            sh = sh.filter(ImageFilter.GaussianBlur(
                max(3, int(font.size * 0.05))))
            img.alpha_composite(sh, (0, max(2, int(h * 0.05))))
        _draw_text_on(ImageDraw.Draw(img), origin, text, font, fill,
                      stroke, sfill, self.opts.emoji)
        return img, pad

    def _layout_text(self):
        s, W, H = self.style, self.W, self.H
        margin, mv = int(W * 0.0926), int(H * 0.052)
        max_w, max_h = W - 2 * margin, H - 2 * mv
        ratio = W / BASE_W
        size = max(12, int((self.slide.size or s.font_size) * ratio))
        minsize = max(12, int(30 * ratio))

        text = self.slide.text.strip()
        if not text:
            self.layers, self.text_full, self.text_alpha = [], None, None
            self.backdrop_layer = None
            return

        while True:
            font = _load_font(s.font_family, size, self.bold)
            lines = _wrap(text, font, max_w)
            line_h = _line_height(font)
            block_h = line_h * len(lines)
            if (not s.fit) or block_h <= max_h or size <= minsize:
                break
            size = max(minsize, int(size * 0.92))

        if s.vpos == "top":
            top = mv
        elif s.vpos == "bottom":
            top = H - mv - block_h
        else:
            top = (H - block_h) // 2

        self.layers = []
        for i, line in enumerate(lines):
            if not line:
                continue
            rgba, pad = self._line_rgba(line, font, ratio, self.fill)
            lw = rgba.width - 2 * pad
            if s.align == "left":
                x = margin
            elif s.align == "right":
                x = W - margin - lw
            else:
                x = (W - lw) // 2
            y = top + i * line_h
            self.layers.append((rgba, int(x - pad), int(y - pad)))

        self.backdrop_layer = None
        if s.backdrop and self.layers:
            bx0 = min(l[1] for l in self.layers)
            by0 = min(l[2] for l in self.layers)
            bx1 = max(l[1] + l[0].width for l in self.layers)
            by1 = max(l[2] + l[0].height for l in self.layers)
            pad_x, pad_y = int(size * 0.45), int(size * 0.30)
            bx0 = max(0, bx0 - pad_x); by0 = max(0, by0 - pad_y)
            bx1 = min(W, bx1 + pad_x); by1 = min(H, by1 + pad_y)
            pill = Image.new("RGBA", (max(2, bx1 - bx0), max(2, by1 - by0)),
                             (0, 0, 0, 0))
            d = ImageDraw.Draw(pill)
            d.rounded_rectangle([0, 0, pill.width - 1, pill.height - 1],
                                radius=pad_y,
                                fill=_hex_rgba(s.backdrop_color,
                                               s.backdrop_alpha))
            self.backdrop_layer = (pill, bx0, by0)

        if self.anim in ("fade", "slide-up", "none"):
            if self.backdrop_layer:
                self.layers.insert(0, self.backdrop_layer)
            full = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            for rgba, px, py in self.layers:
                full.paste(rgba, (px, py), rgba)
            self.text_full = full
            self.text_alpha = full.getchannel("A")
        else:
            self.text_full = self.text_alpha = None

    def _watermark_layer(self):
        W, H = self.W, self.H
        ratio = W / BASE_W
        font = _load_font(self.style.font_family,
                          max(14, int(42 * ratio)), self.bold)
        layer, pad = self._line_rgba(self.opts.watermark, font, ratio)
        img = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        x = (W - (layer.width - 2 * pad)) // 2 - pad
        y = H - int(H * 0.058) - (layer.height - 2 * pad) - pad
        img.paste(layer, (int(x), int(y)), layer)
        return img

    # -------------------------------------------------------------- frame ---
    def _paste_backdrop(self, img, t):
        if not self.backdrop_layer:
            return
        pill, px, py = self.backdrop_layer
        bp_alpha = min(1.0, t / 0.3)
        if bp_alpha < 1.0:
            bp = pill.copy()
            bp.putalpha(pill.getchannel("A").point(lambda v, a=bp_alpha: int(v * a)))
            img.paste(bp, (px, py), bp)
        else:
            img.paste(pill, (px, py), pill)

    def frame_at(self, t: float, progress=None) -> Image.Image:
        t = max(0.0, min(self.dur, t))

        if self.zoom > 1.0:
            k = 1.0 + (self.ZB - 1.0) * _ease(t / self.dur)
            cw = int(self.W * self.ZB / k)
            ch = int(self.H * self.ZB / k)
            cx = (self.bg.width - cw) // 2
            cy = (self.bg.height - ch) // 2
            img = self.bg.crop((cx, cy, cx + cw, cy + ch)) \
                        .resize((self.W, self.H), Image.BILINEAR)
        else:
            img = self.bg.copy()

        a = _ease(t / self.anim_t) if self.anim_t > 0 else 1.0
        if self.anim == "none":
            if self.text_full is not None:
                img.paste(self.text_full, (0, 0), self.text_full)
        elif self.anim == "fade":
            if self.text_full is not None:
                if a >= 0.999:
                    img.paste(self.text_full, (0, 0), self.text_full)
                else:
                    layer = self.text_full.copy()
                    layer.putalpha(self.text_alpha.point(
                        lambda v, a=a: int(v * a)))
                    img.paste(layer, (0, 0), layer)
        elif self.anim == "slide-up":
            if self.text_full is not None:
                dy = int((1 - a) * self.H * 0.05)
                img.paste(self.text_full, (0, dy), self.text_full)
        elif self.anim == "typewriter":
            self._paste_backdrop(img, t)
            fade_l = min(0.22, self.dur * 0.2)
            for i, (rgba, px, py) in enumerate(self.layers):
                u = (t - i * self.stag) / max(0.01, fade_l)
                if u <= 0:
                    continue
                u = min(1.0, u)
                if u >= 1.0:
                    img.paste(rgba, (px, py), rgba)
                else:
                    lay = rgba.copy()
                    lay.putalpha(rgba.getchannel("A").point(
                        lambda v, u=u: int(v * u)))
                    img.paste(lay, (px, py), lay)
        elif self.anim == "pop":
            self._paste_backdrop(img, t)
            pop_d = min(0.3, self.dur * 0.25)
            for i, (rgba, px, py) in enumerate(self.layers):
                u = (t - i * self.stag) / max(0.01, pop_d)
                if u <= 0:
                    continue
                u = min(1.0, u)
                sc = 0.5 + 0.5 * _ease_back(u)
                rw = max(1, int(rgba.width * sc))
                rh = max(1, int(rgba.height * sc))
                rz = rgba.resize((rw, rh), Image.BILINEAR)
                alpha = min(1.0, u * 2.5)
                if alpha < 1.0:
                    rz.putalpha(rz.getchannel("A").point(
                        lambda v, a=alpha: int(v * a)))
                img.paste(rz, (int(px + rgba.width / 2 - rw / 2),
                               int(py + rgba.height / 2 - rh / 2)), rz)

        if self.wm is not None:
            img.paste(self.wm, (0, 0), self.wm)

        if self.prev is not None and self.trans > 0 and t < self.trans:
            u = _ease(t / self.trans)
            img = Image.blend(self.prev, img.convert("RGB"), u)

        if progress is not None:
            self._draw_progress(img, *progress)

        return img.convert("RGB")

    def _draw_progress(self, img, idx, frac, n):
        W, H = self.W, self.H
        pad = int(W * 0.033)
        y = int(H * 0.022)
        bh = max(6, int(H * 0.0052))
        gap = int(bh * 0.9)
        segw = (W - 2 * pad - gap * (n - 1)) / max(1, n)
        strip = Image.new("RGBA", (W, y * 2 + bh), (0, 0, 0, 0))
        d = ImageDraw.Draw(strip)
        rr = hasattr(d, "rounded_rectangle")
        for i in range(n):
            x0 = pad + i * (segw + gap)
            box = [x0, y, x0 + segw, y + bh]
            if rr:
                d.rounded_rectangle(box, radius=bh / 2, fill=(255, 255, 255, 70))
            else:
                d.rectangle(box, fill=(255, 255, 255, 70))
            f = 1.0 if i < idx else (frac if i == idx else 0.0)
            if f > 0:
                box[2] = x0 + segw * f
                if rr:
                    d.rounded_rectangle(box, radius=bh / 2,
                                        fill=(255, 255, 255, 240))
                else:
                    d.rectangle(box, fill=(255, 255, 255, 240))
        img.paste(strip, (0, 0), strip)


# --------------------------------------------------------- moviepy helpers --
def _set_duration(clip, d):
    return (clip.with_duration if hasattr(clip, "with_duration")
            else clip.set_duration)(d)


def _set_audio(clip, a):
    return (clip.with_audio if hasattr(clip, "with_audio")
            else clip.set_audio)(a)


def _subclip(clip, a, b):
    return (clip.subclipped if hasattr(clip, "subclipped")
            else clip.subclip)(a, b)


def _set_volume(clip, v):
    return (clip.with_volume_scaled if hasattr(clip, "with_volume_scaled")
            else clip.volumex)(v)


def _fadeout_audio(clip, d):
    try:
        from moviepy.audio.fx import AudioFadeOut
        return clip.with_effects([AudioFadeOut(d)])
    except Exception:
        pass
    try:
        from moviepy.audio.fx.all import audio_fadeout
        return audio_fadeout(clip, d)
    except Exception:
        return clip


def _fade_video(clip, d, fade_in: bool):
    try:
        from moviepy.video.fx import FadeIn, FadeOut
        return clip.with_effects([FadeIn(d) if fade_in else FadeOut(d)])
    except Exception:
        pass
    try:
        from moviepy.video.fx.all import fadein, fadeout
        return fadein(clip, d) if fade_in else fadeout(clip, d)
    except Exception:
        return clip


def _video_clip(fn, dur):
    try:
        return VideoClip(frame_function=fn, duration=dur)
    except TypeError:
        return VideoClip(make_frame=fn, duration=dur)


def _make_progress_logger(cb):
    try:
        from proglog import ProgressBarLogger
    except Exception:
        return None

    class _Bar(ProgressBarLogger):
        def bars_callback(self, bar, attr, value, old_value=None):
            try:
                info = (self.state.get("bars") or {}).get(bar) or {}
                total = info.get("total") or 0
                idx = value if attr == "index" else (info.get("index") or 0)
                if total:
                    cb(max(0, min(100, int(100 * idx / total))))
            except Exception:
                pass

    return _Bar()


CANCELLED = "__CANCELLED__"


# ---------------------------------------------------------------- workers ---
class ExportWorker(QThread):
    progress = Signal(int)
    stage = Signal(str)
    done = Signal(str)
    canceled = Signal()
    error = Signal(str)

    def __init__(self, slides, style, *, music_path, music_vol, loop,
                 music_off, out_path, size, fps, crf, animate,
                 progress_bar, watermark, emoji):
        super().__init__()
        self.slides = slides
        self.style = style
        self.music_path = music_path
        self.music_vol = music_vol
        self.loop = loop
        self.music_off = music_off
        self.out_path = out_path
        self.size = size
        self.fps = fps
        self.crf = crf
        self.animate = animate
        self.progress_bar = progress_bar
        self.watermark = watermark
        self.emoji = emoji
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            import numpy as np
            W, H = self.size
            opts = RenderOpts(size=(W, H), progress_bar=self.progress_bar,
                              watermark=self.watermark, emoji=self.emoji,
                              kenburns=self.style.kenburns)
            n = len(self.slides)
            clips = []
            last_r = None

            for i, s in enumerate(self.slides):
                if self._cancel:
                    raise RuntimeError(CANCELLED)
                self.stage.emit(f"Rendering slide {i + 1}/{n}…")
                prev = None
                if self.animate and last_r is not None and s.trans > 0:
                    prev = last_r.frame_at(last_r.dur)
                r = SlideRenderer(s, self.style, opts, prev_frame=prev)
                last_r = r
                animated = ((self.animate and r.anim != "none")
                            or r.zoom > 1.0
                            or (r.prev is not None and r.trans > 0))
                if animated or self.progress_bar or self.watermark:
                    def mk(t, _r=r, _i=i, _d=s.duration):
                        if self._cancel:
                            raise RuntimeError(CANCELLED)
                        pr = ((_i, t / _d, n) if self.progress_bar else None)
                        return np.asarray(_r.frame_at(t, pr))
                    clips.append(_video_clip(mk, s.duration))
                else:
                    frame = np.asarray(r.frame_at(s.duration))
                    clips.append(_set_duration(ImageClip(frame), s.duration))
                self.progress.emit(int(5 + 25 * (i + 1) / n))

            self.stage.emit("Stitching slides…")
            video = concatenate_videoclips(clips, method="chain")
            total = sum(s.duration for s in self.slides)
            if self.style.fades and total > 1.6:
                video = _fade_video(video, 0.4, True)
                video = _fade_video(video, 0.4, False)

            # ---------------- audio ----------------
            if self.music_path and os.path.exists(self.music_path):
                self.stage.emit("Adding music…")
                m = AudioFileClip(self.music_path)
                m_duration = m.duration
                start = self.music_off

                if self.loop:
                    reps = int((start + total) / m_duration) + 2
                    m = concatenate_audioclips([m] * reps)
                    m = _set_duration(m, start + total)
                    m = _subclip(m, start, start + total)
                else:
                    if start + total > m_duration:
                        start = max(0.0, m_duration - total)
                    m = _subclip(m, start, start + total)

                m = _set_volume(m, self.music_vol)
                m = _fadeout_audio(m, min(1.5, total / 3))
                video = _set_audio(video, m)

            self.stage.emit("Encoding MP4…")
            logger = _make_progress_logger(
                lambda p: self.progress.emit(35 + int(p * 0.63)))
            threads = max(1, min(8, os.cpu_count() or 1))
            
            try:
                video.write_videofile(
                    self.out_path, fps=self.fps, codec="libx264",
                    audio=bool(self.music_path),  # Safer than audio_codec=None
                    audio_codec="aac" if self.music_path else None,
                    ffmpeg_params=["-pix_fmt", "yuv420p", "-crf", str(self.crf)],
                    threads=threads, logger=logger
                )
            except (IOError, FileNotFoundError) as fe:
                if "ffmpeg" in str(fe).lower() or "imageio" in str(fe).lower():
                    raise RuntimeError(
                        "FFmpeg not found or failed to execute.\n"
                        "Please install FFmpeg and ensure it is added to your system PATH.\n"
                        "Alternatively, run: pip install imageio-ffmpeg"
                    ) from fe
                raise

            try:
                video.close()
            except Exception:
                pass

            self.progress.emit(100)
            self.done.emit(self.out_path)
            
        except Exception as e:
            if CANCELLED in str(e):
                self.canceled.emit()
            else:
                import traceback
                self.error.emit(f"{e}\n\n{traceback.format_exc()[-800:]}")
            
            # Clean up partial file on error/cancel
            try:
                if os.path.exists(self.out_path):
                    os.remove(self.out_path)
            except Exception:
                pass


# ------------------------------------------------------------ preview paint -
class PreviewWidget(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.pm: QPixmap | None = None
        self._prog = None
        self.safe_zones = False
        self.setMinimumSize(360, 480)
        self.setToolTip("Drop an image here → background of the selected "
                        "slide · .txt → import slides · audio → music")

    def set_pixmap(self, pm: QPixmap):
        self.pm = pm
        self.update()

    def set_progress(self, prog):
        self._prog = prog
        self.update()

    def set_safe_zones(self, on: bool):
        self.safe_zones = on
        self.update()

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
        p.fillRect(self.rect(), QColor("#0b0b10"))
        if self.pm is None:
            return
        m = 14
        scale = min((self.width() - 2 * m) / self.pm.width(),
                    (self.height() - 2 * m) / self.pm.height())
        w, h = int(self.pm.width() * scale), int(self.pm.height() * scale)
        x, y = (self.width() - w) // 2, (self.height() - h) // 2
        p.drawPixmap(QRect(x, y, w, h), self.pm)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor("#3a3a4a"), 1))
        p.drawRoundedRect(QRect(x, y, w, h), 12, 12)

        if self.safe_zones:
            p.setPen(QPen(QColor(255, 90, 90, 160), 1, Qt.PenStyle.DashLine))
            p.setBrush(QColor(255, 60, 60, 22))
            p.drawRoundedRect(
                QRect(x + int(w * 0.86), y + int(h * 0.40),
                      int(w * 0.12), int(h * 0.30)), 8, 8)
            p.drawRoundedRect(
                QRect(x + int(w * 0.05), y + int(h * 0.85),
                      int(w * 0.90), int(h * 0.10)), 8, 8)

        if not self._prog:
            return
        idx, frac, n = self._prog
        pad = max(6, int(18 * scale))
        gap = 4
        seg_w = (w - 2 * pad - gap * (n - 1)) / max(1, n)
        y0 = y + pad
        p.setPen(Qt.PenStyle.NoPen)
        for i in range(n):
            x0 = x + pad + i * (seg_w + gap)
            p.setBrush(QColor(255, 255, 255, 55))
            p.drawRoundedRect(QRect(int(x0), y0, int(seg_w), 4), 2, 2)
            f = 1.0 if i < idx else (frac if i == idx else 0.0)
            if f > 0:
                p.setBrush(QColor(255, 255, 255, 235))
                p.drawRoundedRect(
                    QRect(int(x0), y0, max(2, int(seg_w * f)), 4), 2, 2)


class SlideListWidget(QListWidget):
    order_dropped = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setDragDropMode(QListWidget.DragDropMode.InternalMove)
        self.setSelectionMode(QListWidget.SelectionMode.SingleSelection)

    def dropEvent(self, e):
        super().dropEvent(e)
        self.order_dropped.emit()


class SplitDialog(QDialog):
    def __init__(self, parent=None, preset: str = ""):
        super().__init__(parent)
        self.setWindowTitle("Split text into slides")
        self.resize(520, 440)
        v = QVBoxLayout(self)
        v.addWidget(QLabel(
            "Paste or edit the text, choose how to split it, then "
            "replace or append the slides."))
        self.edit = QPlainTextEdit()
        self.edit.setPlaceholderText(
            "Example:\n\nFirst fact goes here…\n\nSecond fact goes here…")
        self.edit.setPlainText(preset)
        v.addWidget(self.edit, 1)
        h = QHBoxLayout()
        h.addWidget(QLabel("Split by"))
        self.mode = QComboBox()
        self.mode.addItems(["Paragraph (blank line)", "Line", "Sentence"])
        h.addWidget(self.mode, 1)
        v.addLayout(h)
        h2 = QHBoxLayout()
        b1 = QPushButton("Replace all slides")
        b1.setObjectName("exportBtn")
        b2 = QPushButton("Append")
        b3 = QPushButton("Cancel")
        b1.clicked.connect(lambda: self.done(1))
        b2.clicked.connect(lambda: self.done(2))
        b3.clicked.connect(self.reject)
        h2.addWidget(b1, 1)
        h2.addWidget(b2)
        h2.addWidget(b3)
        v.addLayout(h2)


def pil_to_pixmap(img: Image.Image) -> QPixmap:
    img = img.convert("RGBA")
    data = img.tobytes("raw", "RGBA")
    qimg = QImage(data, img.width, img.height, img.width * 4,
                  QImage.Format.Format_RGBA8888)
    return QPixmap.fromImage(qimg.copy())


# ---------------------------------------------------------------- main window
QSS = """
QWidget { background-color: #16161d; color: #e8e8ef; font-size: 13px; }
QGroupBox { border: 1px solid #2a2a35; border-radius: 8px;
            margin-top: 14px; padding: 8px; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; color: #9aa0b4; }
QListWidget, QPlainTextEdit, QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
    background: #1e1e28; border: 1px solid #2e2e3c; border-radius: 6px;
    padding: 4px; }
QPushButton { background: #2c2c3a; border: 1px solid #3a3a4c;
              border-radius: 6px; padding: 6px 10px; }
QPushButton:hover { background: #38384c; }
QPushButton:disabled { color: #777; background: #232330; }
QPushButton#exportBtn { background: #7c3aed; border: none; font-weight: 600; }
QPushButton#exportBtn:hover { background: #8d52f0; }
QPushButton#cancelBtn { background: #7f1d1d; border: none; }
QPushButton#cancelBtn:hover { background: #991b1b; }
QPushButton#playBtn { background: #16a34a; border: none; font-weight: 600; }
QPushButton#playBtn:hover { background: #1eb356; }
QPushButton#playBtn:disabled { background: #2b3a2f; color: #777; }
QTabWidget::pane { border: 1px solid #2a2a35; border-radius: 6px; }
QTabBar::tab { background: #1c1c26; padding: 7px 16px; margin-right: 2px;
               border-top-left-radius: 6px; border-top-right-radius: 6px; }
QTabBar::tab:selected { background: #2c2c3a; color: #fff; }
QSlider::groove:horizontal { height: 6px; background: #2e2e3c;
                             border-radius: 3px; }
QSlider::handle:horizontal { width: 14px; margin: -5px 0;
                             border-radius: 7px; background: #7c3aed; }
QProgressBar { border: 1px solid #2e2e3c; border-radius: 6px;
               text-align: center; background: #1e1e28; }
QProgressBar::chunk { background: #7c3aed; border-radius: 5px; }
QScrollBar:vertical { background: #16161d; width: 10px; }
QScrollBar::handle:vertical { background: #3a3a4c; border-radius: 5px;
                              min-height: 30px; }
"""


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.settings = QSettings("ShortsStudio", "ShortsStudio")
        self.slides = [Slide(t, d) for t, d in DEFAULT_SLIDES]
        for s in self.slides[1:]:
            s.trans = 0.35
        self.style = Style()
        self.current = 0
        self.playing = False
        self.play_index = 0
        self.elapsed_ms = 0
        self._loading = False
        self._dirty = False
        self._scrub_guard = False
        self.project_path: str | None = None
        self.worker: ExportWorker | None = None
        self._play_renderers: list = []
        self._play_prev: dict = {}
        self._rcache: dict = {}          # slide idx -> renderer (scrub)
        self._fcache: dict = {}          # frame cache for smooth scrubbing
        self._thumb_cache: dict = {}     # uid -> (key, rendered?)
        self._thumbs_pending: set = set()
        self._style_rev = 1

        # undo/redo
        self._undo: list = []
        self._redo: list = []
        self._pending_burst = False
        self._last_state = self._snap()

        self.play_timer = QTimer(self)
        self.play_timer.setInterval(33)
        self.play_timer.timeout.connect(self._play_tick)

        self.render_timer = QTimer(self)
        self.render_timer.setSingleShot(True)
        self.render_timer.setInterval(120)
        self.render_timer.timeout.connect(self._refresh_preview)

        self.auto_timer = QTimer(self)
        self.auto_timer.setInterval(20000)
        self.auto_timer.timeout.connect(self._autosave)

        self.player = self.audio_out = None
        if MEDIA_OK:
            self.player = QMediaPlayer(self)
            self.audio_out = QAudioOutput(self)
            self.player.setAudioOutput(self.audio_out)
            self.player.mediaStatusChanged.connect(self._media_status)

        self.setAcceptDrops(True)
        self._build_menu()
        self._build_ui()
        self._connect()
        self._load_style_controls()
        self._reload_slide_list(select=0)
        self._update_time_label()
        self._set_title()
        self._load_session()
        self._update_undo_buttons()
        self.auto_timer.start()
        self.render_timer.start()
        QTimer.singleShot(300, self._maybe_recover)
        
        self.setMinimumSize(1000, 680) # Prevent UI from collapsing too small

    # ======================================================== drag & drop ====
    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dropEvent(self, e):
        for url in e.mimeData().urls():
            path = url.toLocalFile()
            if not path or not os.path.exists(path):
                continue
            ext = os.path.splitext(path)[1].lower()
            if ext in IMG_EXTS:
                self._push_undo()
                self.slides[self.current].bg_image = path
                self._commit()
                self._dirty_set()
                self._load_editor(self.current)
                self.status.setText(f"Background set → {os.path.basename(path)}")
            elif ext == ".txt":
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        text = f.read()
                    self._split_text_flow(text)
                except Exception as ex:
                    QMessageBox.critical(self, "Import failed", str(ex))
            elif ext in AUD_EXTS:
                self.music_edit.setText(path)
                self.status.setText(f"Music set → {os.path.basename(path)}")

    # ============================================================ spacebar ===
    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Space:
            fw = QApplication.focusWidget()
            editors = (QPlainTextEdit, QLineEdit, QComboBox, QAbstractSpinBox,
                       QListWidget)
            if fw is None or not isinstance(fw, editors):
                if self.playing:
                    self._stop_preview()
                else:
                    self._on_play()
                return
        super().keyPressEvent(e)

    # ================================================================ menu ===
    def _build_menu(self):
        mb = self.menuBar()
        m_file = mb.addMenu("&File")
        m_file.addAction("New project", QKeySequence.StandardKey.New,
                         self._new_project)
        m_file.addAction("Open…", QKeySequence.StandardKey.Open,
                         self._open_project)
        m_file.addAction("Save", QKeySequence.StandardKey.Save,
                         self._save_project)
        m_file.addAction("Save As…", QKeySequence.StandardKey.SaveAs,
                         self._save_project_as)
        self.recent_menu = m_file.addMenu("Recent projects")
        self.recent_menu.aboutToShow.connect(self._rebuild_recent)
        m_file.addSeparator()
        m_file.addAction("Exit", QKeySequence.StandardKey.Quit, self.close)

        m_edit = mb.addMenu("&Edit")
        self.act_undo = m_edit.addAction("Undo", QKeySequence.StandardKey.Undo,
                                         self._do_undo)
        self.act_redo = m_edit.addAction("Redo", QKeySequence.StandardKey.Redo,
                                         self._do_redo)
        m_edit.addSeparator()
        m_edit.addAction("Fit durations to reading time", self._fit_durations)
        m_edit.addAction("Fill backgrounds from folder…", self._fill_bg_folder)

        m_help = mb.addMenu("&Help")
        m_help.addAction("About", self._about)

    def _rebuild_recent(self):
        self.recent_menu.clear()
        recents = self._get_recents()
        if not recents:
            self.recent_menu.addAction("(none)").setEnabled(False)
            return
        for path in recents:
            self.recent_menu.addAction(
                os.path.basename(path),
                lambda p=path: self._load_project(p))

    def _get_recents(self) -> list:
        val = self.settings.value("recents", [])
        return [p for p in (val if isinstance(val, list) else [val])
                if isinstance(p, str) and os.path.exists(p)]

    def _push_recent(self, path):
        recents = [p for p in self._get_recents() if p != path]
        recents.insert(0, path)
        self.settings.setValue("recents", recents[:8])

    def _about(self):
        QMessageBox.about(self, f"About {APP_NAME}",
                          f"<b>{APP_NAME} {APP_VERSION}</b><br><br>"
                          "Make YouTube Shorts from text slides, images "
                          "and music.<br><br>"
                          "Shortcuts: Ctrl+N/O/S/E · Ctrl+Z/Y undo/redo · "
                          "F5 or Space play · Esc stop · Ctrl+←/→ slides · "
                          "Ctrl+↑/↓ reorder<br><br>"
                          "Drag & drop: image → slide background, "
                          ".txt → new slides, audio → music")

    # ================================================================== UI ===
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(8, 8, 8, 8)
        split = QSplitter(Qt.Orientation.Horizontal)
        root.addWidget(split)

        panel = QWidget()
        panel.setMaximumWidth(520)
        v = QVBoxLayout(panel)
        v.setContentsMargins(0, 0, 0, 0)
        self.tabs = QTabWidget()
        v.addWidget(self.tabs)

        self.tabs.addTab(self._tab_slides(), "Slides")
        self.tabs.addTab(self._tab_style(), "Style")
        self.tabs.addTab(self._tab_audio(), "Audio")
        self.tabs.addTab(self._tab_export(), "Export")

        scroll = QScrollArea()
        scroll.setWidget(panel)
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setMinimumWidth(460)
        split.addWidget(scroll)

        right = QWidget()
        rv = QVBoxLayout(right)
        self.preview = PreviewWidget()
        rv.addWidget(self.preview, 1)

        scrub_row = QHBoxLayout()
        self.t_cur = QLabel("0.0s")
        self.t_cur.setFixedWidth(52)
        self.scrub = QSlider(Qt.Orientation.Horizontal)
        self.scrub.setRange(0, 1000)
        self.loopplay_check = QCheckBox("Loop")
        scrub_row.addWidget(self.t_cur)
        scrub_row.addWidget(self.scrub, 1)
        scrub_row.addWidget(self.loopplay_check)
        rv.addLayout(scrub_row)

        row = QHBoxLayout()
        self.play_btn = QPushButton("▶  Play  (F5 / Space)")
        self.play_btn.setObjectName("playBtn")
        self.stop_btn = QPushButton("■  Stop  (Esc)")
        self.stop_btn.setEnabled(False)
        self.safe_check = QCheckBox("Safe zones")
        self.safe_check.setToolTip(
            "Show where YouTube's UI (title, buttons) covers the video")
        self.time_label = QLabel("")
        row.addWidget(self.play_btn)
        row.addWidget(self.stop_btn)
        row.addWidget(self.safe_check)
        row.addStretch(1)
        row.addWidget(self.time_label)
        rv.addLayout(row)
        right.setMinimumWidth(380)
        split.addWidget(right)
        split.setSizes([490, 930])

    # ---- tabs ---------------------------------------------------------------
    def _tab_slides(self) -> QWidget:
        w = QWidget()
        v = QVBoxLayout(w)
        v.setSpacing(10)

        g = QGroupBox("Slides  (thumbnails · drag to reorder)")
        gv = QVBoxLayout(g)
        self.slide_list = SlideListWidget()
        self.slide_list.setIconSize(QSize(*THUMB_SIZE))
        self.slide_list.setFixedHeight(190)
        gv.addWidget(self.slide_list)
        row = QHBoxLayout()
        self.b_add = QPushButton("Add")
        self.b_dup = QPushButton("Duplicate")
        self.b_del = QPushButton("Delete")
        self.b_up = QPushButton("↑")
        self.b_down = QPushButton("↓")
        self.b_undo = QPushButton("↶")
        self.b_undo.setToolTip("Undo (Ctrl+Z)")
        self.b_redo = QPushButton("↷")
        self.b_redo.setToolTip("Redo (Ctrl+Shift+Z)")
        for b in (self.b_add, self.b_dup, self.b_del, self.b_up, self.b_down,
                  self.b_undo, self.b_redo):
            row.addWidget(b)
        gv.addLayout(row)
        v.addWidget(g)

        g = QGroupBox("Selected slide")
        gv = QVBoxLayout(g)
        self.text_edit = QPlainTextEdit()
        self.text_edit.setPlaceholderText(
            "What should viewers read?\nEnter = line break. Text auto-wraps.")
        self.text_edit.setFixedHeight(110)
        gv.addWidget(self.text_edit)
        row = QHBoxLayout()
        row.addWidget(QLabel("Show for"))
        self.dur_spin = QDoubleSpinBox()
        self.dur_spin.setRange(0.5, 180.0)
        self.dur_spin.setSingleStep(0.5)
        self.dur_spin.setDecimals(1)
        self.dur_spin.setSuffix(" s")
        row.addWidget(self.dur_spin)
        self.read_lbl = QLabel("")
        self.read_lbl.setStyleSheet("color:#9aa0b4;")
        row.addWidget(self.read_lbl, 1)
        gv.addLayout(row)

        row = QHBoxLayout()
        row.addWidget(QLabel("Crossfade in"))
        self.trans_spin = QDoubleSpinBox()
        self.trans_spin.setRange(0.0, 1.0)
        self.trans_spin.setSingleStep(0.05)
        self.trans_spin.setDecimals(2)
        self.trans_spin.setSuffix(" s")
        self.trans_spin.setToolTip(
            "Blend from the previous slide's last frame at this slide's "
            "start (ignored on slide 1).")
        row.addWidget(self.trans_spin)
        self.b_trans_all = QPushButton("All")
        self.b_trans_all.setToolTip("Use this crossfade on every slide")
        row.addWidget(self.b_trans_all)
        row.addStretch(1)
        gv.addLayout(row)

        row = QHBoxLayout()
        row.addWidget(QLabel("Animation"))
        self.anim_combo = QComboBox()
        self.anim_combo.addItems(ANIM_LABELS)
        row.addWidget(self.anim_combo, 1)
        self.b_anim_all = QPushButton("Apply to all")
        row.addWidget(self.b_anim_all)
        gv.addLayout(row)

        row = QHBoxLayout()
        row.addWidget(QLabel("Text override"))
        self.oc_btn = QPushButton()
        self.oc_btn.setFixedHeight(28)
        self.oc_btn.setMinimumWidth(90)
        self.oc_btn.setToolTip("Per-slide text color (empty = style color)")
        self.b_oc_auto = QPushButton("Auto")
        self.b_oc_auto.setToolTip("Back to the style's text color")
        row.addWidget(self.oc_btn, 1)
        row.addWidget(self.b_oc_auto)
        gv.addLayout(row)

        row = QHBoxLayout()
        row.addWidget(QLabel("Size override"))
        self.size_o_spin = QSpinBox()
        self.size_o_spin.setRange(0, 240)
        self.size_o_spin.setSuffix(" px  (0 = inherit)")
        self.size_o_spin.setToolTip("Per-slide font size; 0 uses the Style tab")
        row.addWidget(self.size_o_spin, 1)
        gv.addLayout(row)

        row = QHBoxLayout()
        row.addWidget(QLabel("Background image"))
        self.bg_lbl = QLabel("none")
        self.bg_lbl.setStyleSheet("color:#9aa0b4;")
        row.addWidget(self.bg_lbl, 1)
        self.b_bgpic = QPushButton("Image…")
        self.b_bgpclr = QPushButton("✕")
        row.addWidget(self.b_bgpic)
        row.addWidget(self.b_bgpclr)
        gv.addLayout(row)
        v.addWidget(g)

        g = QGroupBox("Pacing & bulk text")
        hv = QVBoxLayout(g)
        row = QHBoxLayout()
        self.b_fitdurs = QPushButton("Fit durations to reading time")
        self.b_fitdurs.setToolTip(
            "Set each slide's length from its word count (~2.5 words/sec)")
        row.addWidget(self.b_fitdurs)
        self.hint_lbl = QLabel("")
        self.hint_lbl.setStyleSheet("color:#f59e0b;")
        row.addWidget(self.hint_lbl, 1)
        hv.addLayout(row)
        row = QHBoxLayout()
        self.b_split = QPushButton("✂ Split long text…")
        self.b_import = QPushButton("📄 Import .txt…")
        self.b_folder = QPushButton("🖼 Folder → backgrounds")
        self.b_folder.setToolTip(
            "Assign images from a folder to the slides, round-robin")
        row.addWidget(self.b_split)
        row.addWidget(self.b_import)
        row.addWidget(self.b_folder)
        hv.addLayout(row)
        v.addWidget(g)
        v.addStretch(1)
        return w

    def _tab_style(self) -> QWidget:
        w = QWidget()
        v = QVBoxLayout(w)

        g = QGroupBox("Text")
        form = QFormLayout(g)
        self.font_combo = QFontComboBox()
        form.addRow("Font", self.font_combo)
        self.bold_check = QCheckBox("Bold (uses the family's bold file)")
        form.addRow("", self.bold_check)
        self.size_spin = QSpinBox()
        self.size_spin.setRange(24, 240)
        self.size_spin.setValue(self.style.font_size)
        form.addRow("Size (px @1080)", self.size_spin)
        row = QHBoxLayout()
        self.align_combo = QComboBox()
        self.align_combo.addItems(["Left", "Center", "Right"])
        self.vpos_combo = QComboBox()
        self.vpos_combo.addItems(["Top", "Middle", "Bottom"])
        row.addWidget(self.align_combo)
        row.addWidget(self.vpos_combo)
        form.addRow("Align / height", row)
        self.txt_btn = QPushButton()
        self.txt_btn.setFixedHeight(30)
        form.addRow("Text color", self.txt_btn)
        row = QHBoxLayout()
        self.outline_check = QCheckBox("on")
        self.out_width = QSpinBox()
        self.out_width.setRange(0, 20)
        self.out_width.setValue(self.style.outline_width)
        self.out_btn = QPushButton()
        self.out_btn.setFixedHeight(30)
        row.addWidget(self.outline_check)
        row.addWidget(QLabel("width"))
        row.addWidget(self.out_width)
        row.addWidget(self.out_btn, 1)
        form.addRow("Outline", row)
        self.shadow_check = QCheckBox("Soft shadow")
        form.addRow("", self.shadow_check)
        row = QHBoxLayout()
        self.backdrop_check = QCheckBox("Pill")
        self.backdrop_check.setToolTip(
            "Rounded translucent pill behind the text (caption style)")
        self.bd_btn = QPushButton()
        self.bd_btn.setFixedHeight(30)
        self.bd_alpha = QSlider(Qt.Orientation.Horizontal)
        self.bd_alpha.setRange(20, 230)
        self.bd_alpha.setValue(self.style.backdrop_alpha)
        row.addWidget(self.backdrop_check)
        row.addWidget(self.bd_btn, 1)
        row.addWidget(self.bd_alpha, 1)
        form.addRow("Backdrop", row)
        self.fit_check = QCheckBox("Auto-shrink text to fit")
        form.addRow("", self.fit_check)
        v.addWidget(g)

        g = QGroupBox("Background & overlays")
        form = QFormLayout(g)
        row = QHBoxLayout()
        self.bg1_btn = QPushButton()
        self.bg1_btn.setFixedHeight(30)
        self.grad_check = QCheckBox("gradient ↓")
        self.bg2_btn = QPushButton()
        self.bg2_btn.setFixedHeight(30)
        row.addWidget(self.bg1_btn, 1)
        row.addWidget(self.grad_check)
        row.addWidget(self.bg2_btn, 1)
        form.addRow("Colors", row)
        row = QHBoxLayout()
        row.addWidget(QLabel("Dim"))
        self.dim_slider = QSlider(Qt.Orientation.Horizontal)
        self.dim_slider.setRange(0, 80)
        self.dim_slider.setValue(self.style.dim)
        self.dim_slider.setToolTip(
            "Darken the background so text stays readable over photos")
        self.dim_lbl = QLabel("0%")
        self.dim_lbl.setFixedWidth(34)
        row.addWidget(self.dim_slider, 1)
        row.addWidget(self.dim_lbl)
        form.addRow("Dim overlay", row)
        self.kb_check = QCheckBox("Ken Burns zoom on image backgrounds")
        form.addRow("", self.kb_check)
        self.prog_check = QCheckBox("Story progress bars (baked in)")
        form.addRow("", self.prog_check)
        row = QHBoxLayout()
        self.wm_check = QCheckBox("Watermark")
        self.wm_edit = QLineEdit(self.style.watermark_text)
        self.wm_edit.setPlaceholderText("@yourhandle")
        row.addWidget(self.wm_check)
        row.addWidget(self.wm_edit, 1)
        form.addRow("", row)
        self.emoji_check = QCheckBox(
            "Emoji support" + ("" if PILMOJI_OK
                               else "  (needs: pip install pilmoji)"))
        self.emoji_check.setEnabled(PILMOJI_OK)
        form.addRow("", self.emoji_check)
        self.b_theme = QPushButton("🎲 Random theme")
        form.addRow("", self.b_theme)
        v.addWidget(g)
        v.addStretch(1)
        return w

    def _tab_audio(self) -> QWidget:
        w = QWidget()
        v = QVBoxLayout(w)

        g = QGroupBox("Background music")
        mv = QVBoxLayout(g)
        row = QHBoxLayout()
        self.music_edit = QLineEdit()
        self.music_edit.setReadOnly(True)
        self.music_edit.setPlaceholderText("no music — pick, or drop a file…")
        self.b_browse = QPushButton("Browse…")
        self.b_clear = QPushButton("✕")
        row.addWidget(self.music_edit, 1)
        row.addWidget(self.b_browse)
        row.addWidget(self.b_clear)
        mv.addLayout(row)
        row = QHBoxLayout()
        row.addWidget(QLabel("Volume"))
        self.vol_slider = QSlider(Qt.Orientation.Horizontal)
        self.vol_slider.setRange(0, 100)
        self.vol_slider.setValue(70)
        self.vol_lbl = QLabel("70%")
        self.vol_lbl.setFixedWidth(36)
        row.addWidget(self.vol_slider, 1)
        row.addWidget(self.vol_lbl)
        mv.addLayout(row)
        row = QHBoxLayout()
        row.addWidget(QLabel("Start at"))
        self.music_off = QSpinBox()
        self.music_off.setRange(0, 3600)
        self.music_off.setSuffix(" s")
        self.music_off.setToolTip("Skip this far into the track before it plays")
        row.addWidget(self.music_off)
        row.addStretch(1)
        mv.addLayout(row)
        self.loop_check = QCheckBox("Loop if shorter than the video")
        self.loop_check.setChecked(True)
        mv.addWidget(self.loop_check)
        mv.addWidget(QLabel(
            "Plays during preview and is mixed into the exported MP4\n"
            "(with a short fade-out at the end)."))
        v.addWidget(g)
        v.addStretch(1)
        return w

    def _tab_export(self) -> QWidget:
        w = QWidget()
        v = QVBoxLayout(w)
        g = QGroupBox("Export settings")
        form = QFormLayout(g)
        self.res_combo = QComboBox()
        self.res_combo.addItems(["1080 × 1920 (recommended)",
                                 "720 × 1280 (faster)"])
        form.addRow("Resolution", self.res_combo)
        self.fps_combo = QComboBox()
        self.fps_combo.addItems(["30 fps", "24 fps"])
        form.addRow("Frame rate", self.fps_combo)
        self.q_combo = QComboBox()
        self.q_combo.addItems(["High quality (CRF 18)",
                               "Medium (CRF 23)",
                               "Small file (CRF 28)"])
        form.addRow("Quality", self.q_combo)
        self.anim_export_check = QCheckBox(
            "Render animations, crossfades & effects (uncheck = fastest)")
        self.anim_export_check.setChecked(True)
        form.addRow("", self.anim_export_check)
        self.b_png = QPushButton("Save current slide as PNG (1080×1920)")
        self.b_png.setToolTip("Handy for thumbnails")
        form.addRow("", self.b_png)
        v.addWidget(g)

        g = QGroupBox("Export")
        ev = QVBoxLayout(g)
        self.total_lbl = QLabel("")
        ev.addWidget(self.total_lbl)
        self.export_btn = QPushButton("Export MP4…  (Ctrl+E)")
        self.export_btn.setObjectName("exportBtn")
        self.export_btn.setMinimumHeight(40)
        if not MOVIEPY_OK:
            self.export_btn.setToolTip(
                "moviepy is not installed — run:  pip install moviepy")
        ev.addWidget(self.export_btn)
        row = QHBoxLayout()
        self.cancel_btn = QPushButton("Cancel export")
        self.cancel_btn.setObjectName("cancelBtn")
        self.cancel_btn.setEnabled(False)
        self.cancel_btn.hide()
        row.addWidget(self.cancel_btn, 1)
        ev.addLayout(row)
        self.progress = QProgressBar()
        ev.addWidget(self.progress)
        self.status = QLabel("Ready.")
        self.status.setWordWrap(True)
        ev.addWidget(self.status)
        v.addWidget(g)
        v.addStretch(1)
        return w

    # ============================================================ connect ====
    def _connect(self):
        self.slide_list.currentRowChanged.connect(self._on_slide_selected)
        self.slide_list.order_dropped.connect(self._on_reordered)
        self.b_add.clicked.connect(self._add_slide)
        self.b_dup.clicked.connect(self._dup_slide)
        self.b_del.clicked.connect(self._del_slide)
        self.b_up.clicked.connect(lambda: self._move_slide(-1))
        self.b_down.clicked.connect(lambda: self._move_slide(+1))
        self.b_undo.clicked.connect(self._do_undo)
        self.b_redo.clicked.connect(self._do_redo)

        self.text_edit.textChanged.connect(self._on_text_changed)
        self.dur_spin.valueChanged.connect(self._on_dur_changed)
        self.trans_spin.valueChanged.connect(self._on_trans_changed)
        self.b_trans_all.clicked.connect(self._trans_all)
        self.anim_combo.currentIndexChanged.connect(self._on_anim_changed)
        self.b_anim_all.clicked.connect(self._anim_all)
        self.oc_btn.clicked.connect(self._on_oc_color)
        self.b_oc_auto.clicked.connect(self._on_oc_auto)
        self.size_o_spin.valueChanged.connect(self._on_size_o_changed)
        self.b_bgpic.clicked.connect(self._pick_bg_image)
        self.b_bgpclr.clicked.connect(self._clear_bg_image)
        self.b_fitdurs.clicked.connect(self._fit_durations)
        self.b_split.clicked.connect(lambda: self._split_text_flow(""))
        self.b_import.clicked.connect(self._import_txt)
        self.b_folder.clicked.connect(self._fill_bg_folder)

        self.font_combo.currentFontChanged.connect(
            lambda _f: self._style_changed())
        self.bold_check.toggled.connect(lambda _b: self._style_changed())
        for widget in (self.size_spin, self.out_width):
            widget.valueChanged.connect(lambda _v: self._style_changed())
        for combo in (self.align_combo, self.vpos_combo):
            combo.currentIndexChanged.connect(lambda _i: self._style_changed())
        for chk in (self.fit_check, self.grad_check, self.outline_check,
                    self.shadow_check, self.backdrop_check, self.kb_check,
                    self.prog_check, self.emoji_check):
            chk.toggled.connect(lambda _b: self._style_changed())
        self.bd_alpha.valueChanged.connect(lambda _v: self._style_changed())
        self.dim_slider.valueChanged.connect(self._on_dim_changed)
        self.wm_edit.textChanged.connect(self._style_changed)

        self.txt_btn.clicked.connect(
            lambda: self._pick_color("text_color", self.txt_btn))
        self.out_btn.clicked.connect(
            lambda: self._pick_color("outline_color", self.out_btn))
        self.bg1_btn.clicked.connect(
            lambda: self._pick_color("bg1", self.bg1_btn))
        self.bg2_btn.clicked.connect(
            lambda: self._pick_color("bg2", self.bg2_btn))
        self.bd_btn.clicked.connect(
            lambda: self._pick_color("backdrop_color", self.bd_btn))
        self.b_theme.clicked.connect(self._random_theme)

        self.b_browse.clicked.connect(self._browse_music)
        self.b_clear.clicked.connect(self.music_edit.clear)
        self.music_edit.textChanged.connect(lambda _t: self._mark_dirty())
        self.vol_slider.valueChanged.connect(
            lambda v_: self.vol_lbl.setText(f"{v_}%"))
        self.vol_slider.valueChanged.connect(lambda _v: self._mark_dirty())
        self.loop_check.toggled.connect(lambda _b: self._mark_dirty())
        self.music_off.valueChanged.connect(lambda _v: self._mark_dirty())

        self.scrub.valueChanged.connect(self._on_scrub)
        self.play_btn.clicked.connect(self._on_play)
        self.stop_btn.clicked.connect(self._stop_preview)
        self.safe_check.toggled.connect(self.preview.set_safe_zones)
        self.b_png.clicked.connect(self._export_frame)
        self.export_btn.clicked.connect(self._export)
        self.cancel_btn.clicked.connect(
            lambda: self.worker and self.worker.cancel())

        QShortcut(QKeySequence("Ctrl+D"), self, self._dup_slide)
        QShortcut(QKeySequence("Ctrl+E"), self, self._export)
        QShortcut(QKeySequence("F5"), self, self._on_play)
        QShortcut(QKeySequence("Esc"), self, self._stop_preview)
        for key, delta in (("Ctrl+Up", -1), ("Ctrl+Down", +1)):
            sc = QShortcut(QKeySequence(key), self.slide_list)
            sc.setContext(Qt.ShortcutContext.WidgetShortcut)
            sc.activated.connect(lambda d=delta: self._move_slide(d))
        for key, delta in (("Ctrl+Left", -1), ("Ctrl+Right", +1)):
            sc = QShortcut(QKeySequence(key), self.slide_list)
            sc.setContext(Qt.ShortcutContext.WidgetShortcut)
            sc.activated.connect(
                lambda d=delta: self.slide_list.setCurrentRow(
                    max(0, min(len(self.slides) - 1,
                               self.slide_list.currentRow() + d))))
        sc = QShortcut(QKeySequence(Qt.Key.Key_Delete), self.slide_list)
        sc.setContext(Qt.ShortcutContext.WidgetShortcut)
        sc.activated.connect(self._del_slide)

    # ====================================================== undo / redo ======
    def _snap(self):
        return (copy.deepcopy(self.slides), copy.deepcopy(self.style))

    def _push_undo(self):
        self._undo.append(self._last_state)
        if len(self._undo) > 60:
            self._undo.pop(0)
        self._redo.clear()
        self._update_undo_buttons()

    def _commit(self):
        self._last_state = self._snap()
        self._pending_burst = False

    def _reset_history(self):
        self._undo.clear()
        self._redo.clear()
        self._pending_burst = False
        self._commit()
        self._update_undo_buttons()

    def _update_undo_buttons(self):
        self.b_undo.setEnabled(bool(self._undo))
        self.b_redo.setEnabled(bool(self._redo))
        self.act_undo.setEnabled(bool(self._undo))
        self.act_redo.setEnabled(bool(self._redo))

    def _do_undo(self):
        if not self._undo:
            return
        self._stop_preview()
        self._redo.append(self._snap())
        self.slides, self.style = self._undo.pop()
        self._pending_burst = False
        self._commit()
        self._after_swap()
        self._dirty_set()
        self._update_undo_buttons()

    def _do_redo(self):
        if not self._redo:
            return
        self._stop_preview()
        self._undo.append(self._snap())
        self.slides, self.style = self._redo.pop()
        self._pending_burst = False
        self._commit()
        self._after_swap()
        self._dirty_set()
        self._update_undo_buttons()

    def _after_swap(self):
        self._bump_style()
        self._load_style_controls()
        self._reload_slide_list(select=min(self.current, len(self.slides) - 1))

    # ======================================================== caches =========
    def _bump_style(self):
        self._style_rev += 1
        self._thumbs_pending.update(range(len(self.slides)))

    def _frame_cached(self, i, t) -> QPixmap:
        s = self.slides[i]
        key = (s.uid, round(t * 30), s.text, s.anim, s.trans, s.bg_image,
               s.duration, s.color, s.size, self._style_rev)
        pm = self._fcache.get(key)
        if pm is None:
            r = self._scrub_pair(i)
            pr = ((i, t / max(0.01, r.dur), len(self.slides))
                  if self.style.progress_bar else None)
            pm = pil_to_pixmap(r.frame_at(t, pr))
            self._fcache[key] = pm
            while len(self._fcache) > 30:
                self._fcache.pop(next(iter(self._fcache)))
        return pm

    def _update_thumb(self, i):
        if not (0 <= i < len(self.slides)):
            return
        if not (0 <= i < self.slide_list.count()):
            return
        s = self.slides[i]
        key = (s.text, s.anim, s.bg_image, s.duration, s.color, s.size,
               self._style_rev)
        hit = self._thumb_cache.get(s.uid)
        if hit is not None and hit[0] == key:
            return
        try:
            opts = RenderOpts(size=THUMB_RENDER, progress_bar=False,
                              watermark="",
                              emoji=self.style.emoji and PILMOJI_OK,
                              kenburns=False)
            r = SlideRenderer(s, self.style, opts)
            pm = pil_to_pixmap(r.frame_at(r.dur)).scaled(
                THUMB_SIZE[0] * 2, THUMB_SIZE[1] * 2,
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation)
            self.slide_list.item(i).setIcon(QIcon(pm))
            self._thumb_cache[s.uid] = (key, True)
        except Exception:
            pass

    # ======================================================== slides logic ===
    def _current_opts(self) -> RenderOpts:
        return RenderOpts(size=PREVIEW_SIZE,
                          progress_bar=self.style.progress_bar,
                          watermark=self._watermark_string(),
                          emoji=self.style.emoji and PILMOJI_OK,
                          kenburns=self.style.kenburns)

    def _watermark_string(self) -> str:
        if self.style.watermark_on and self.wm_edit.text().strip():
            t = self.wm_edit.text().strip()
            return t if t.startswith("@") else "@" + t
        return ""

    def total_duration(self):
        return sum(s.duration for s in self.slides)

    def _reload_slide_list(self, select=None):
        self._loading = True
        self.slide_list.clear()
        for i, s in enumerate(self.slides):
            item = QListWidgetItem()
            item.setData(Qt.ItemDataRole.UserRole, s.uid)
            self.slide_list.addItem(item)
            self._set_item_text(i)
        if select is None:
            select = min(self.current, len(self.slides) - 1)
        self.slide_list.setCurrentRow(select)
        self._loading = False
        self._load_editor(select)
        self._update_time_label()
        self._update_buttons()
        self._thumbs_pending.update(range(len(self.slides)))
        self.render_timer.start()

    def _set_item_text(self, i):
        s = self.slides[i]
        first = s.text.strip().splitlines()
        label = first[0][:34] if first else "(empty)"
        est = read_speed(s.text)
        warn = "⚠ " if est > s.duration + 0.05 else ""
        item = self.slide_list.item(i)
        item.setText(f"{i + 1}.  {warn}{label}")
        item.setToolTip(f"estimated read time ≈ {est:.1f} s "
                        f"(shown {s.duration:.1f} s)"
                        + ("\n⚠ may be too fast to read!" if warn else ""))

    def _refresh_item(self, i):
        if 0 <= i < len(self.slides):
            self._set_item_text(i)

    def _load_editor(self, idx):
        self.current = max(0, min(idx, len(self.slides) - 1))
        s = self.slides[self.current]
        self._loading = True
        self.text_edit.setPlainText(s.text)
        self.dur_spin.setValue(s.duration)
        self.trans_spin.setValue(s.trans)
        self.anim_combo.setCurrentIndex(ANIMS.index(s.anim)
                                        if s.anim in ANIMS else 0)
        self.size_o_spin.setValue(s.size)
        self._apply_swatch(self.oc_btn, s.color or self.style.text_color)
        if s.color:
            self.oc_btn.setToolTip(f"Per-slide text color: {s.color}")
        else:
            self.oc_btn.setToolTip("Per-slide text color (empty = style color)")
        self.b_oc_auto.setEnabled(bool(s.color))
        fm = self.bg_lbl.fontMetrics()
        self.bg_lbl.setText(fm.elidedText(s.bg_image or "none",
                                          Qt.TextElideMode.ElideMiddle, 160))
        self._loading = False
        self._show_frame(self.current)
        self._sync_scrub_to_slide(self.current)
        self._update_buttons()
        self._update_read_label()

    def _on_slide_selected(self, row):
        if self._loading or row < 0:
            return
        if self.playing:
            self._stop_preview()
        self._load_editor(row)

    def _on_reordered(self):
        self._stop_preview()
        self._push_undo()
        order = [self.slide_list.item(i).data(Qt.ItemDataRole.UserRole)
                 for i in range(self.slide_list.count())]
        self.slides.sort(key=lambda s: order.index(s.uid))
        for i in range(len(self.slides)):
            self._set_item_text(i)
        self.current = max(0, self.slide_list.currentRow())
        self._load_editor(self.current)
        self._update_buttons()
        self._commit()
        self._dirty_set()

    def _add_slide(self):
        self._stop_preview()
        self._push_undo()
        self.slides.insert(self.current + 1, Slide("", 4.0))
        self._reload_slide_list(select=self.current + 1)
        self._commit()
        self._dirty_set()
        self.text_edit.setFocus()

    def _dup_slide(self):
        self._stop_preview()
        self._push_undo()
        s = copy.deepcopy(self.slides[self.current])
        s.uid = uuid.uuid4().hex
        self.slides.insert(self.current + 1, s)
        self._reload_slide_list(select=self.current + 1)
        self._commit()
        self._dirty_set()

    def _del_slide(self):
        if len(self.slides) <= 1:
            return
        self._stop_preview()
        self._push_undo()
        del self.slides[self.current]
        self._reload_slide_list(select=min(self.current, len(self.slides) - 1))
        self._commit()
        self._dirty_set()

    def _move_slide(self, delta):
        j = self.current + delta
        if not (0 <= j < len(self.slides)):
            return
        self._stop_preview()
        self._push_undo()
        self.slides[self.current], self.slides[j] = \
            self.slides[j], self.slides[self.current]
        self._reload_slide_list(select=j)
        self._commit()
        self._dirty_set()

    def _update_buttons(self):
        self.b_del.setEnabled(len(self.slides) > 1)
        self.b_up.setEnabled(self.current > 0)
        self.b_down.setEnabled(self.current < len(self.slides) - 1)

    def _on_text_changed(self):
        if self._loading:
            return
        self.slides[self.current].text = self.text_edit.toPlainText()
        self._refresh_item(self.current)
        self._update_read_label()
        self._thumbs_pending.add(self.current)
        self._mark_dirty()
        self.render_timer.start()

    def _on_dur_changed(self, val):
        if self._loading:
            return
        self.slides[self.current].duration = float(val)
        self._refresh_item(self.current)
        self._update_read_label()
        self._update_time_label()
        self._mark_dirty()

    def _on_trans_changed(self, val):
        if self._loading:
            return
        self.slides[self.current].trans = float(val)
        self._mark_dirty()

    def _trans_all(self):
        self._push_undo()
        v = float(self.trans_spin.value())
        for s in self.slides:
            s.trans = v
        self._commit()
        self._dirty_set()

    def _on_anim_changed(self, idx):
        if self._loading:
            return
        self.slides[self.current].anim = ANIMS[idx]
        self._mark_dirty()

    def _anim_all(self):
        self._push_undo()
        anim = ANIMS[self.anim_combo.currentIndex()]
        for s in self.slides:
            s.anim = anim
        self._commit()
        self._dirty_set()

    def _on_oc_color(self):
        s = self.slides[self.current]
        c = QColorDialog.getColor(QColor(s.color or self.style.text_color),
                                  self, "Text color for this slide")
        if c.isValid():
            self._push_undo()
            s.color = c.name()
            self._apply_swatch(self.oc_btn, c.name())
            self.oc_btn.setToolTip(f"Per-slide text color: {s.color}")
            self.b_oc_auto.setEnabled(True)
            self._commit()
            self._dirty_set()
            self.render_timer.start()

    def _on_oc_auto(self):
        s = self.slides[self.current]
        if not s.color:
            return
        self._push_undo()
        s.color = ""
        self._apply_swatch(self.oc_btn, self.style.text_color)
        self.oc_btn.setToolTip("Per-slide text color (empty = style color)")
        self.b_oc_auto.setEnabled(False)
        self._commit()
        self._dirty_set()
        self.render_timer.start()

    def _on_size_o_changed(self, val):
        if self._loading:
            return
        self.slides[self.current].size = int(val)
        self._mark_dirty()
        self.render_timer.start()

    def _update_read_label(self):
        s = self.slides[self.current]
        est = read_speed(s.text)
        self.read_lbl.setText(f"read ≈ {est:.1f}s")
        ok = est <= s.duration + 0.05
        self.hint_lbl.setText("" if ok
                              else f"⚠ slide {self.current + 1} may be too "
                                   f"fast to read ({est:.1f}s needed)")

    def _fit_durations(self):
        self._push_undo()
        for i, s in enumerate(self.slides):
            s.duration = max(1.5, min(20.0, read_speed(s.text)))
            self._refresh_item(i)
        self._load_editor(self.current)
        self._update_time_label()
        self._commit()
        self._dirty_set()

    def _pick_bg_image(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Background image for this slide", "",
            "Images (*.jpg *.jpeg *.png *.webp *.bmp);;All files (*)")
        if not path:
            return
        self._push_undo()
        self.slides[self.current].bg_image = path
        fm = self.bg_lbl.fontMetrics()
        self.bg_lbl.setText(fm.elidedText(path, Qt.TextElideMode.ElideMiddle,
                                          160))
        self._commit()
        self._dirty_set()
        self.render_timer.start()

    def _clear_bg_image(self):
        if not self.slides[self.current].bg_image:
            return
        self._push_undo()
        self.slides[self.current].bg_image = ""
        self.bg_lbl.setText("none")
        self._commit()
        self._dirty_set()
        self.render_timer.start()

    def _fill_bg_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Pick an image folder")
        if not folder:
            return
        files = [os.path.join(folder, f)
                 for f in sorted(os.listdir(folder))
                 if f.lower().endswith(IMG_EXTS)]
        if not files:
            QMessageBox.information(self, "No images",
                                    "That folder has no jpg/png/webp/bmp files.")
            return
        self._push_undo()
        for i, s in enumerate(self.slides):
            s.bg_image = files[i % len(files)]
        self._commit()
        self._dirty_set()
        self._load_editor(self.current)
        self.status.setText(f"Assigned {len(files)} images across "
                            f"{len(self.slides)} slides (round-robin).")

    # ======================================================= bulk text =======
    def _split_text_flow(self, preset: str):
        dlg = SplitDialog(self, preset)
        r = dlg.exec()
        if r == 0:
            return
        text = dlg.edit.toPlainText().strip()
        if not text:
            return
        mode = dlg.mode.currentIndex()
        if mode == 0:
            chunks = [p.strip() for p in re.split(r"\n\s*\n", text) if p.strip()]
        elif mode == 1:
            chunks = [l.strip() for l in text.splitlines() if l.strip()]
        else:
            chunks = split_sentences(text)
        if not chunks:
            return
        self._stop_preview()
        self._push_undo()
        new = [Slide(c, min(20.0, max(1.5, read_speed(c))),
                     anim=self.slides[self.current].anim,
                     trans=self.slides[self.current].trans)
               for c in chunks]
        if r == 1:
            self.slides = new
            self.current = 0
        else:
            self.slides.extend(new)
            self.current = len(self.slides) - len(new)
        self._commit()
        self._dirty_set()
        self._reload_slide_list(select=self.current)

    def _import_txt(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Import text file", "", "Text (*.txt);;All files (*)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                text = f.read()
        except Exception as e:
            QMessageBox.critical(self, "Import failed", str(e))
            return
        self._split_text_flow(text)

    # =========================================================== style =======
    def _style_changed(self):
        if self._loading:
            return
        self._read_style_controls()
        self._bump_style()
        self._mark_dirty()
        self.render_timer.start()

    def _on_dim_changed(self, v):
        self.dim_lbl.setText(f"{v}%")
        self._style_changed()

    def _read_style_controls(self):
        s = self.style
        s.font_family = self.font_combo.currentFont().family()
        s.bold = self.bold_check.isChecked()
        s.font_size = self.size_spin.value()
        s.align = ("left", "center", "right")[self.align_combo.currentIndex()]
        s.vpos = ("top", "middle", "bottom")[self.vpos_combo.currentIndex()]
        s.fit = self.fit_check.isChecked()
        s.gradient = self.grad_check.isChecked()
        s.outline = self.outline_check.isChecked()
        s.outline_width = self.out_width.value()
        s.shadow = self.shadow_check.isChecked()
        s.backdrop = self.backdrop_check.isChecked()
        s.backdrop_alpha = self.bd_alpha.value()
        s.dim = self.dim_slider.value()
        s.kenburns = self.kb_check.isChecked()
        s.progress_bar = self.prog_check.isChecked()
        s.watermark_on = self.wm_check.isChecked()
        s.emoji = self.emoji_check.isChecked()
        self.bg2_btn.setEnabled(s.gradient)
        self.wm_edit.setEnabled(s.watermark_on)
        self.bd_btn.setEnabled(s.backdrop)
        self.bd_alpha.setEnabled(s.backdrop)

    def _load_style_controls(self):
        s = self.style
        self._loading = True
        self.font_combo.setCurrentFont(QFont(s.font_family))
        self.bold_check.setChecked(s.bold)
        self.size_spin.setValue(s.font_size)
        self.align_combo.setCurrentIndex(["left", "center", "right"].index(s.align))
        self.vpos_combo.setCurrentIndex(["top", "middle", "bottom"].index(s.vpos))
        self.outline_check.setChecked(s.outline)
        self.out_width.setValue(s.outline_width)
        self.shadow_check.setChecked(s.shadow)
        self.backdrop_check.setChecked(s.backdrop)
        self.bd_alpha.setValue(s.backdrop_alpha)
        self.dim_slider.setValue(s.dim)
        self.dim_lbl.setText(f"{s.dim}%")
        self.fit_check.setChecked(s.fit)
        self.grad_check.setChecked(s.gradient)
        self.kb_check.setChecked(s.kenburns)
        self.prog_check.setChecked(s.progress_bar)
        self.wm_check.setChecked(s.watermark_on)
        self.wm_edit.setText(s.watermark_text)
        self.emoji_check.setChecked(s.emoji and PILMOJI_OK)
        self._apply_swatch(self.txt_btn, s.text_color)
        self._apply_swatch(self.out_btn, s.outline_color)
        self._apply_swatch(self.bg1_btn, s.bg1)
        self._apply_swatch(self.bg2_btn, s.bg2)
        self._apply_swatch(self.bd_btn, s.backdrop_color)
        self._apply_swatch(self.oc_btn,
                           self.slides[self.current].color or s.text_color)
        self.b_oc_auto.setEnabled(bool(self.slides[self.current].color))
        self._loading = False
        self.bg2_btn.setEnabled(s.gradient)
        self.wm_edit.setEnabled(s.watermark_on)
        self.bd_btn.setEnabled(s.backdrop)
        self.bd_alpha.setEnabled(s.backdrop)

    def _apply_swatch(self, btn, hex_color):
        c = QColor(hex_color)
        lum = 0.2126 * c.red() + 0.7152 * c.green() + 0.0722 * c.blue()
        fg = "#101014" if lum > 150 else "#ffffff"
        btn.setText(hex_color)
        btn.setStyleSheet(
            "QPushButton { background-color: %s; color: %s;"
            " border: 1px solid #55555f; border-radius: 6px; }"
            % (hex_color, fg))

    def _pick_color(self, attr, btn):
        c = QColorDialog.getColor(QColor(getattr(self.style, attr)), self,
                                  "Pick a color")
        if c.isValid():
            setattr(self.style, attr, c.name())
            self._apply_swatch(btn, c.name())
            self._style_changed()

    def _random_theme(self):
        self._push_undo()
        bg1, bg2, fg = random.choice(PALETTES)
        self.style.bg1, self.style.bg2, self.style.text_color = bg1, bg2, fg
        self._apply_swatch(self.bg1_btn, bg1)
        self._apply_swatch(self.bg2_btn, bg2)
        self._apply_swatch(self.txt_btn, fg)
        self._commit()
        self._bump_style()
        self._dirty_set()
        self.render_timer.start()

    # ========================================================= preview =======
    def _refresh_preview(self):
        self._rcache.clear()
        self._fcache.clear()
        for i in sorted(self._thumbs_pending):
            self._update_thumb(i)
        self._thumbs_pending.clear()
        if not self.playing:
            self._show_frame(self.current)

    def _scrub_pair(self, i: int) -> SlideRenderer:
        r = self._rcache.get(i)
        if r is None:
            prev = None
            if i > 0 and self.slides[i].trans > 0:
                prev_r = self._scrub_pair(i - 1)
                prev = prev_r.frame_at(prev_r.dur)
            r = SlideRenderer(self.slides[i], self.style, self._current_opts(),
                              prev_frame=prev)
            self._rcache[i] = r
        return r

    def _show_frame(self, idx):
        idx = max(0, min(idx, len(self.slides) - 1))
        r = self._scrub_pair(idx)
        self.preview.set_pixmap(self._frame_cached(idx, r.dur))

    def _show_frame_at(self, i, t):
        self.preview.set_pixmap(self._frame_cached(i, t))

    def _pos_to_slide(self, sec: float):
        acc = 0.0
        for i, s in enumerate(self.slides):
            if sec < acc + s.duration or i == len(self.slides) - 1:
                return i, max(0.0, min(sec - acc, s.duration))
            acc += s.duration
        return 0, 0.0

    def _on_scrub(self, val):
        if self.playing or self._scrub_guard:
            return
        i, t = self._pos_to_slide(val / 1000.0)
        self._show_frame_at(i, t)
        self.t_cur.setText(f"{val / 1000.0:.1f}s")

    def _update_scrub_range(self):
        total_ms = max(1, int(round(self.total_duration() * 1000)))
        self._scrub_guard = True
        self.scrub.setRange(0, total_ms)
        self._scrub_guard = False

    def _sync_scrub_to_slide(self, idx):
        if not self.slides:
            return
        start = int(sum(s.duration for s in self.slides[:idx]) * 1000)
        self._scrub_guard = True
        self.scrub.setValue(start)
        self._scrub_guard = False
        self.t_cur.setText(f"{start / 1000.0:.1f}s")

    def _on_play(self):
        if self.playing:
            return
        self.playing = True
        self.play_index = 0
        self.elapsed_ms = 0
        self._rcache.clear()
        self._fcache.clear()
        opts = self._current_opts()
        self._play_renderers = [SlideRenderer(s, self.style, opts)
                                for s in self.slides]
        self._play_prev = {}
        for i in range(1, len(self.slides)):
            if self.slides[i].trans > 0:
                pr = self._play_renderers[i - 1]
                self._play_prev[i] = pr.frame_at(pr.dur)
                self._play_renderers[i].prev = self._play_prev[i]
                self._play_renderers[i].trans = min(
                    self.slides[i].trans, self._play_renderers[i].dur * 0.8)
        self.preview.set_progress((0, 0.0, len(self.slides)))
        self._show_playing_frame(0, 0.0)
        self.play_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)
        self._start_music()

    def _show_playing_frame(self, i, local_t):
        r = self._play_renderers[i]
        pr = ((i, local_t / r.dur, len(self._play_renderers))
              if self.style.progress_bar else None)
        self.preview.set_pixmap(pil_to_pixmap(r.frame_at(local_t, pr)))

    def _play_tick(self):
        self.elapsed_ms += self.play_timer.interval()
        total_ms = int(self.total_duration() * 1000)
        if self.elapsed_ms >= total_ms:
            if self.loopplay_check.isChecked():
                self.elapsed_ms = 0
                self._show_playing_frame(0, 0.0)
                if self.player is not None:
                    self.player.setPosition(self.music_off.value() * 1000)
                    self.player.play()
            else:
                self._stop_preview()
            return
        acc = 0
        for i, s in enumerate(self.slides):
            d = int(s.duration * 1000)
            if self.elapsed_ms < acc + d:
                local = (self.elapsed_ms - acc) / 1000.0
                self.play_index = i
                self._show_playing_frame(i, local)
                self.preview.set_progress(
                    (i, (self.elapsed_ms - acc) / d, len(self.slides)))
                self._update_time_label(self.elapsed_ms / 1000)
                self._scrub_guard = True
                self.scrub.setValue(self.elapsed_ms)
                self._scrub_guard = False
                self.t_cur.setText(f"{self.elapsed_ms / 1000.0:.1f}s")
                break
            acc += d

    def _stop_preview(self):
        self.playing = False
        self.play_timer.stop()
        if self.player is not None:
            self.player.stop()
        self.preview.set_progress(None)
        self.play_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)
        self._show_frame(self.current)
        self._sync_scrub_to_slide(self.current)
        self._update_time_label()

    def _update_time_label(self, elapsed=None):
        total = self.total_duration()
        if elapsed is None:
            self.time_label.setText(
                f"{len(self.slides)} slides · {total:.1f} s")
            self.total_lbl.setText(
                f"{len(self.slides)} slides · total {total:.1f} s"
                + (f"   ⚠ over {SHORTS_LIMIT_S} s (Shorts limit)"
                   if total > SHORTS_LIMIT_S else ""))
            self.total_lbl.setStyleSheet(
                "color:#ef4444;" if total > SHORTS_LIMIT_S else "color:#9aa0b4;")
            self._update_scrub_range()
        else:
            self.time_label.setText(f"{elapsed:5.1f} / {total:.1f} s")

    # ============================================================ music ======
    def _media_status(self, status):
        if (status == QMediaPlayer.MediaStatus.LoadedMedia and self.playing
                and self.music_off.value() > 0):
            self.player.setPosition(self.music_off.value() * 1000)

    def _start_music(self):
        if self.player is None:
            return
        path = self.music_edit.text().strip()
        if path and os.path.exists(path):
            self.audio_out.setVolume(self.vol_slider.value() / 100.0)
            self.player.setSource(QUrl.fromLocalFile(path))
            self.player.setLoopCount(-1 if self.loop_check.isChecked() else 1)
            self.player.play()
            if self.music_off.value() > 0:
                self.player.setPosition(self.music_off.value() * 1000)

    def _browse_music(self):
        start = self.settings.value("last_music_dir", "")
        path, _ = QFileDialog.getOpenFileName(
            self, "Pick background music", start,
            "Audio (*.mp3 *.wav *.m4a *.aac *.ogg *.flac);;All files (*)")
        if path:
            self.music_edit.setText(path)
            self.settings.setValue("last_music_dir", os.path.dirname(path))

    # ============================================================ project ====
    def _mark_dirty(self):
        if self._loading:
            return
        if not self._pending_burst:
            self._pending_burst = True
            QTimer.singleShot(600, self._flush_burst)
        self._dirty_set()

    def _flush_burst(self):
        if not self._pending_burst:
            return
        self._pending_burst = False
        self._push_undo()
        self._commit()

    def _dirty_set(self):
        if not self._dirty:
            self._dirty = True
            self._set_title()

    def _set_title(self):
        name = os.path.basename(self.project_path) if self.project_path \
            else "Untitled"
        self.setWindowTitle(f"{'* ' if self._dirty else ''}{name} — "
                            f"{APP_NAME}")

    def _project_dict(self) -> dict:
        return {
            "app": "shorts-studio", "version": 3,
            "slides": [{"text": s.text, "duration": s.duration,
                        "anim": s.anim, "bg_image": s.bg_image,
                        "trans": s.trans, "color": s.color,
                        "size": s.size} for s in self.slides],
            "style": asdict(self.style),
            "music": {"path": self.music_edit.text(),
                      "volume": self.vol_slider.value(),
                      "loop": self.loop_check.isChecked(),
                      "offset": self.music_off.value()},
            "export": {"res": self.res_combo.currentIndex(),
                       "fps": self.fps_combo.currentIndex(),
                       "quality": self.q_combo.currentIndex(),
                       "animate": self.anim_export_check.isChecked()},
        }

    def _apply_project_dict(self, data):
        self._loading = True
        style_fields = {f.name for f in fields(Style)}
        self.style = Style(**{k: v for k, v in
                              data.get("style", {}).items()
                              if k in style_fields})
        self.slides = [Slide(**{k: v for k, v in sl.items()
                                if k in {f.name for f in fields(Slide)}})
                       for sl in data.get("slides", [])]
        if not self.slides:
            self.slides = [Slide("", 4.0)]
        m = data.get("music", {})
        self.music_edit.setText(m.get("path", "") or "")
        self.vol_slider.setValue(int(m.get("volume", 70)))
        self.loop_check.setChecked(bool(m.get("loop", True)))
        self.music_off.setValue(int(m.get("offset", 0)))
        ex = data.get("export", {})
        self.res_combo.setCurrentIndex(int(ex.get("res", 0)))
        self.fps_combo.setCurrentIndex(int(ex.get("fps", 0)))
        self.q_combo.setCurrentIndex(int(ex.get("quality", 0)))
        self.anim_export_check.setChecked(bool(ex.get("animate", True)))
        self._load_style_controls()
        self._loading = False
        self._bump_style()
        self._reload_slide_list(select=0)

    def _new_project(self):
        if not self._confirm_discard():
            return
        self._stop_preview()
        self.slides = [Slide(t, d) for t, d in DEFAULT_SLIDES]
        for s in self.slides[1:]:
            s.trans = 0.35
        self.style = Style()
        self.project_path = None
        self._dirty = False
        self._bump_style()
        self._load_style_controls()
        self._reload_slide_list(select=0)
        self._reset_history()
        self._set_title()
        self._delete_recovery()

    def _confirm_discard(self) -> bool:
        if not self._dirty:
            return True
        r = QMessageBox.question(
            self, "Unsaved changes",
            "You have unsaved changes. Save them?",
            QMessageBox.StandardButton.Save |
            QMessageBox.StandardButton.Discard |
            QMessageBox.StandardButton.Cancel)
        if r == QMessageBox.StandardButton.Save:
            return self._save_project()
        return r == QMessageBox.StandardButton.Discard

    def _open_project(self):
        if not self._confirm_discard():
            return
        start = self.settings.value("last_proj_dir", "")
        path, _ = QFileDialog.getOpenFileName(
            self, "Open project", start, "Shorts project (*.shorts.json)")
        if path:
            self._load_project(path)

    def _load_project(self, path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._stop_preview()
            self._apply_project_dict(data)
            self.project_path = path
            self._dirty = False
            self._reset_history()
            self._push_recent(path)
            self.settings.setValue("last_proj_dir", os.path.dirname(path))
            self._set_title()
            self._delete_recovery()
            missing = sorted({s.bg_image for s in self.slides
                              if s.bg_image and not os.path.exists(s.bg_image)})
            if missing:
                QMessageBox.warning(
                    self, "Missing images",
                    "These background images could not be found "
                    "(gradient will be used):\n\n"
                    + "\n".join(missing[:8]))
        except Exception as e:
            QMessageBox.critical(self, "Open failed", f"Could not open:\n{e}")

    def _save_project(self) -> bool:
        if not self.project_path:
            return self._save_project_as()
        try:
            with open(self.project_path, "w", encoding="utf-8") as f:
                json.dump(self._project_dict(), f, ensure_ascii=False, indent=1)
            self._dirty = False
            self._push_recent(self.project_path)
            self._set_title()
            self._delete_recovery()
            return True
        except Exception as e:
            QMessageBox.critical(self, "Save failed", str(e))
            return False

    def _save_project_as(self) -> bool:
        start = self.project_path or os.path.join(
            os.path.expanduser("~"), "my_short.shorts.json")
        path, _ = QFileDialog.getSaveFileName(
            self, "Save project", start, "Shorts project (*.shorts.json)")
        if not path:
            return False
        if not path.endswith(".shorts.json"):
            path += ".shorts.json"
        self.project_path = path
        return self._save_project()

    # =========================================================== recovery ====
    def _autosave(self):
        if not self._dirty:
            return
        try:
            with open(RECOVERY_PATH, "w", encoding="utf-8") as f:
                json.dump(self._project_dict(), f, ensure_ascii=False)
        except Exception:
            pass

    def _delete_recovery(self):
        try:
            if os.path.exists(RECOVERY_PATH):
                os.remove(RECOVERY_PATH)
        except Exception:
            pass

    def _maybe_recover(self):
        if not os.path.exists(RECOVERY_PATH):
            return
        r = QMessageBox.question(
            self, "Recover session?",
            "An auto-saved session was found (the app may have closed "
            "unexpectedly).\n\nRestore it?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        if r != QMessageBox.StandardButton.Yes:
            self._delete_recovery()
            return
        try:
            with open(RECOVERY_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            self._stop_preview()
            self._apply_project_dict(data)
            self.project_path = None
            self._dirty = True
            self._reset_history()
            self._set_title()
            self.status.setText("Session recovered — remember to Save.")
        except Exception:
            self._delete_recovery()

    # ============================================================= session ===
    def _save_session(self):
        try:
            self.settings.setValue(
                "session_style", json.dumps(asdict(self.style)))
            self.settings.setValue("session_music", json.dumps(
                {"path": self.music_edit.text(),
                 "vol": self.vol_slider.value(),
                 "loop": self.loop_check.isChecked(),
                 "off": self.music_off.value()}))
            self.settings.setValue("session_export", json.dumps(
                {"res": self.res_combo.currentIndex(),
                 "fps": self.fps_combo.currentIndex(),
                 "q": self.q_combo.currentIndex(),
                 "anim": self.anim_export_check.isChecked()}))
        except Exception:
            pass

    def _load_session(self):
        self._loading = True
        try:
            raw = self.settings.value("session_style", "")
            if raw:
                data = json.loads(raw)
                fl = {f.name for f in fields(Style)}
                self.style = Style(**{k: v for k, v in data.items()
                                      if k in fl})
                self._load_style_controls()
            raw = self.settings.value("session_music", "")
            if raw:
                d = json.loads(raw)
                self.music_edit.setText(d.get("path", "") or "")
                self.vol_slider.setValue(int(d.get("vol", 70)))
                self.loop_check.setChecked(bool(d.get("loop", True)))
                self.music_off.setValue(int(d.get("off", 0)))
            raw = self.settings.value("session_export", "")
            if raw:
                d = json.loads(raw)
                self.res_combo.setCurrentIndex(int(d.get("res", 0)))
                self.fps_combo.setCurrentIndex(int(d.get("fps", 0)))
                self.q_combo.setCurrentIndex(int(d.get("q", 0)))
                self.anim_export_check.setChecked(bool(d.get("anim", True)))
        except Exception:
            pass
        self._loading = False
        self._bump_style()

    # ============================================================= export ====
    def _export_frame(self):
        opts = RenderOpts(size=(1080, 1920),
                          progress_bar=self.style.progress_bar,
                          watermark=self._watermark_string(),
                          emoji=self.style.emoji and PILMOJI_OK,
                          kenburns=self.style.kenburns)
        r = SlideRenderer(self.slides[self.current], self.style, opts)
        start = self.settings.value("last_export_dir", "") \
            or os.path.expanduser("~")
        path, _ = QFileDialog.getSaveFileName(
            self, "Save slide as PNG",
            os.path.join(start, f"slide_{self.current + 1}.png"),
            "PNG image (*.png)")
        if not path:
            return
        if not path.lower().endswith(".png"):
            path += ".png"
        try:
            r.frame_at(r.dur).save(path)
            self.status.setText(f"Saved image → {path}")
        except Exception as e:
            QMessageBox.critical(self, "Save failed", str(e))

    def _export(self):
        if not MOVIEPY_OK:
            QMessageBox.warning(self, "moviepy not installed",
                                "Video export needs moviepy:\n\n"
                                "    pip install moviepy")
            return
        self._stop_preview()
        total = self.total_duration()
        if total > SHORTS_LIMIT_S:
            r = QMessageBox.question(
                self, "Long video",
                f"This video is {total:.0f} s (YouTube Shorts limit is "
                f"{SHORTS_LIMIT_S} s).\nExport anyway?")
            if r != QMessageBox.StandardButton.Yes:
                return

        missing = sorted({s.bg_image for s in self.slides
                          if s.bg_image and not os.path.exists(s.bg_image)})
        mp = self.music_edit.text().strip()
        if mp and not os.path.exists(mp):
            missing.append(mp + "   (music)")
        if missing:
            r = QMessageBox.question(
                self, "Missing files",
                "Some files could not be found and will be skipped:\n\n"
                + "\n".join(missing[:8]) + "\n\nExport anyway?")
            if r != QMessageBox.StandardButton.Yes:
                return

        start = self.settings.value("last_export_dir", "")
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Short",
            os.path.join(start or os.path.expanduser("~"), "short.mp4"),
            "MP4 video (*.mp4)")
        if not path:
            return
        if not path.lower().endswith(".mp4"):
            path += ".mp4"
        self.settings.setValue("last_export_dir", os.path.dirname(path))

        size = (1080, 1920) if self.res_combo.currentIndex() == 0 \
            else (720, 1280)
        fps = 30 if self.fps_combo.currentIndex() == 0 else 24
        crf = (18, 23, 28)[self.q_combo.currentIndex()]

        self._set_export_ui(True)
        self.progress.setValue(0)
        self.status.setText("Exporting…")
        self.worker = ExportWorker(
            copy.deepcopy(self.slides), copy.deepcopy(self.style),
            music_path=mp or None,
            music_vol=self.vol_slider.value() / 100.0,
            loop=self.loop_check.isChecked(),
            music_off=float(self.music_off.value()),
            out_path=path, size=size, fps=fps, crf=crf,
            animate=self.anim_export_check.isChecked(),
            progress_bar=self.style.progress_bar,
            watermark=self._watermark_string(),
            emoji=self.style.emoji and PILMOJI_OK)
        self.worker.progress.connect(self.progress.setValue)
        self.worker.stage.connect(self.status.setText)
        self.worker.done.connect(self._export_done)
        self.worker.canceled.connect(self._export_canceled)
        self.worker.error.connect(self._export_error)
        self.worker.finished.connect(self._export_cleanup)
        self.worker.start()

    def _set_export_ui(self, busy):
        self.export_btn.setEnabled(not busy)
        self.cancel_btn.setVisible(busy)
        self.cancel_btn.setEnabled(busy)

    def _export_done(self, path):
        self.status.setText(f"Done → {path}")
        if QMessageBox.question(
                self, "Export finished",
                f"Saved to:\n{path}\n\nOpen the folder?"
        ) == QMessageBox.StandardButton.Yes:
            QDesktopServices.openUrl(QUrl.fromLocalFile(os.path.dirname(path)))

    def _export_canceled(self):
        self.status.setText("Export canceled.")

    def _export_error(self, msg):
        self.status.setText("Export failed — see message.")
        QMessageBox.critical(self, "Export failed", msg)

    def _export_cleanup(self):
        self._set_export_ui(False)
        self.worker = None

    # ============================================================== close ====
    def closeEvent(self, ev):
        if self.worker is not None and self.worker.isRunning():
            QMessageBox.warning(self, "Busy",
                                "Please wait for the export to finish "
                                "(or cancel it).")
            ev.ignore()
            return
        self._save_session()
        if self._dirty and not self._confirm_discard():
            ev.ignore()
            return
        self._delete_recovery()
        super().closeEvent(ev)


def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(QSS)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()