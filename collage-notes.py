#!/usr/bin/env python3
"""
collage-notes - paste images, get an auto-arranged A4 collage page.

* Native Qt6 app: runs on Wayland and X11 (Qt picks the backend itself).
* Ctrl+V pastes an image straight from the clipboard (or turn on
  "Auto-capture clipboard" and every copied image is added by itself).
* Images are packed into justified rows that fill the A4 page, sized so
  nothing is tiny and nothing is huge; pages are added as needed.
* Per image: resize, rotate, crop (to cut ads), float/overlap, reorder.
* Export PDF (A4), print, or copy a finished page back to the clipboard.

Needs: PyQt6 (or PySide6).   Run: python3 collage-notes.py [images...]
"""
import sys, os, math, json, zipfile, hashlib, random, time

try:
    from PyQt6 import QtCore, QtGui, QtWidgets, QtPrintSupport
except ImportError:                                   # pragma: no cover
    from PySide6 import QtCore, QtGui, QtWidgets, QtPrintSupport

Qt = QtCore.Qt
QRectF, QPointF, QTimer = QtCore.QRectF, QtCore.QPointF, QtCore.QTimer
QImage, QPainter, QColor, QPen, QBrush = (QtGui.QImage, QtGui.QPainter,
                                          QtGui.QColor, QtGui.QPen, QtGui.QBrush)
QAction, QKeySequence = QtGui.QAction, QtGui.QKeySequence
W_ = QtWidgets

A4_W, A4_H = 210.0, 297.0          # mm; the whole scene is measured in mm
PAGE_GAP = 14.0
MAX_SIDE = 2600                    # cap pasted images (keeps RAM low)
PREVIEW_SIDE = 1100                # screen-resolution copy
MAX_ROW = 6                        # max images per row
ACCENT = QColor(30, 136, 229)


# --------------------------------------------------------------------------
# model
# --------------------------------------------------------------------------
class Pic:
    def __init__(self, img):
        self.img = img
        self._prev = None
        self.crop = [0.0, 0.0, 1.0, 1.0]   # x0,y0,x1,y1 normalised
        self.rot90 = 0                     # user rotation (quarter turns, cw)
        self.auto_rot = 0                  # chosen by auto-rotate
        self.lock_rot = False              # user rotated -> auto leaves it
        self.fine = 0.0                    # free tilt in degrees (floating only)
        self.weight = 1.0                  # relative size inside the flow
        self.free = False                  # floating: ignored by the flow
        self.rect = [0.0, 0.0, 50.0, 50.0]  # floating rect in scene mm
        self.z = 0
        self.cell = None                   # (x,y,w,h) set by layout

    @property
    def preview(self):
        if self._prev is None:
            if max(self.img.width(), self.img.height()) <= PREVIEW_SIDE:
                self._prev = self.img
            else:
                self._prev = self.img.scaled(
                    PREVIEW_SIDE, PREVIEW_SIDE, Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation)
        return self._prev

    def total_rot(self):
        return (self.rot90 + self.auto_rot) % 4

    def aspect(self):
        c = self.crop
        a = ((c[2] - c[0]) * self.img.width()) / max(1e-6, (c[3] - c[1]) * self.img.height())
        return 1.0 / a if self.total_rot() % 2 else a

    def geom(self):
        if self.free:
            return tuple(self.rect)
        return self.cell or (0, 0, 40, 40)

    def refit_free(self):
        x, y, w, h = self.rect
        cx, cy, a = x + w / 2, y + h / 2, self.aspect()
        nw = math.sqrt(w * h * a)
        nh = nw / a
        self.rect = [cx - nw / 2, cy - nh / 2, nw, nh]

    def state(self):
        return dict(crop=list(self.crop), rot90=self.rot90, lock_rot=self.lock_rot,
                    fine=self.fine, weight=self.weight, free=self.free,
                    rect=list(self.rect), z=self.z)

    def set_state(self, s):
        for k, v in s.items():
            setattr(self, k, list(v) if isinstance(v, list) else v)


class Cfg:
    rows = 4.0        # target rows per page  (fewer rows = bigger pictures)
    gap = 2.0         # mm between pictures (negative = overlap)
    margin = 8.0      # mm page margin
    autorot = False
    smart = True      # ignore paste order, search for the best arrangement
    border = True
    guides = True


# --------------------------------------------------------------------------
# layout engine (pure python, no Qt)
# --------------------------------------------------------------------------
def justify(asp, wts, W, g, T, hmax):
    """Split pictures (in order) into rows whose height is close to T*weight.
    Every row is stretched to exactly fill width W.  Returns [(i, j, h)]."""
    n = len(asp)
    S = [0.0]
    for a in asp:
        S.append(S[-1] + a)
    INF = 1e18
    best = [INF] * (n + 1)
    prev = [0] * (n + 1)
    best[0] = 0.0
    for j in range(1, n + 1):
        wm = 0.0
        for i in range(j - 1, max(-1, j - MAX_ROW - 1), -1):
            wm = max(wm, wts[i])
            h = (W - (j - i - 1) * g) / (S[j] - S[i])
            t = T * wm
            c = ((h - t) / t) ** 2 + 0.03
            if h > hmax:
                c += 4 * ((h - hmax) / t) ** 2
            v = best[i] + c
            if v < best[j]:
                best[j], prev[j] = v, i
    rows, j = [], n
    while j > 0:
        i = prev[j]
        h = (W - (j - i - 1) * g) / (S[j] - S[i])
        rows.append((i, j, min(h, hmax)))
        j = i
    rows.reverse()
    return rows


def rows_height(rows, g):
    return sum(r[2] for r in rows) + g * (len(rows) - 1)


def compute_layout(auto, cfg):
    """Assign .cell to every flowing picture. Returns number of pages."""
    if not auto:
        return 1
    m, g = cfg.margin, cfg.gap
    W, Hp = A4_W - 2 * m, A4_H - 2 * m
    asp = [p.aspect() for p in auto]
    wts = [p.weight for p in auto]
    hmax = Hp * 0.8
    T = (Hp - g * (cfg.rows - 1)) / cfg.rows

    rows = justify(asp, wts, W, g, T, hmax)
    pages, cur, used = [], [], 0.0
    for (i, j, h) in rows:                       # greedy pagination by rows
        need = h + (g if cur else 0)
        if cur and used + need > Hp + 1e-6:
            pages.append((cur[0][0], cur[-1][1]))
            cur, used, need = [], 0.0, h
        cur.append((i, j, h))
        used += need
    pages.append((cur[0][0], cur[-1][1]))

    for pi, (lo, hi) in enumerate(pages):        # refit each page to fill it
        last = pi == len(pages) - 1
        sa, sw = asp[lo:hi], wts[lo:hi]

        def attempt(t):
            r = justify(sa, sw, W, g, t, hmax)
            return r, rows_height(r, g)

        top = T * (1.35 if last else 2.2)
        r, tot = attempt(top)
        if tot > Hp:
            lo_t, hi_t = T * 0.15, top
            r, _ = attempt(lo_t)
            for _ in range(16):
                mid = (lo_t + hi_t) / 2
                rr, tt = attempt(mid)
                if tt <= Hp:
                    lo_t, r = mid, rr
                else:
                    hi_t = mid
        y = pi * (A4_H + PAGE_GAP) + m
        for (i, j, h) in r:
            widths = [asp[lo + k] * h for k in range(i, j)]
            x = m + (W - (sum(widths) + g * (j - i - 1))) / 2
            for k, wd in zip(range(i, j), widths):
                auto[lo + k].cell = (x, y, wd, h)
                x += wd + g
            y += h + g
    return len(pages)


def layout_score(auto, npages):
    areas = [math.log(max(1.0, p.cell[2] * p.cell[3])) for p in auto]
    mean = sum(areas) / len(areas)
    sd = math.sqrt(sum((a - mean) ** 2 for a in areas) / len(areas))
    return npages * 10 + sd


def fit_score(auto, npages, cfg):
    """Lower = better.  Few pages, every picture close to the target row
    height (not tiny, not huge), similar sizes, and no half-empty last page."""
    m, g = cfg.margin, cfg.gap
    Hp = A4_H - 2 * m
    T = (Hp - g * (cfg.rows - 1)) / cfg.rows
    dev = sum(math.log(max(1e-3, p.cell[3] / (T * p.weight))) ** 2 for p in auto) / len(auto)
    areas = [math.log(max(1.0, p.cell[2] * p.cell[3])) for p in auto]
    mean = sum(areas) / len(areas)
    sd = math.sqrt(sum((a - mean) ** 2 for a in areas) / len(areas))
    y0 = (npages - 1) * (A4_H + PAGE_GAP) + m
    bottom = max(p.cell[1] + p.cell[3] for p in auto)
    waste = max(0.0, 1.0 - (bottom - y0) / Hp)
    return npages * 10 + 2 * dev + sd + waste


_SMART = {"key": None, "order": []}


def smart_order(auto, cfg, budget=0.15):
    """Reorder the flowing pictures (paste order is ignored) to get the best
    page fill.  Tries sensible seeds, then hill-climbs with swaps/moves."""
    n = len(auto)
    if n < 3:
        return list(auto)
    key = (tuple((id(p), round(p.aspect(), 4), p.weight) for p in auto),
           cfg.rows, cfg.gap, cfg.margin)
    if _SMART["key"] == key:
        return list(_SMART["order"])

    def ev(order):
        return fit_score(order, compute_layout(order, cfg), cfg)

    have = {id(p) for p in auto}
    kept = [p for p in _SMART["order"] if id(p) in have]
    seen = {id(p) for p in kept}
    seeded = kept + [p for p in auto if id(p) not in seen]   # keeps old layout stable
    by_asp = sorted(auto, key=lambda p: p.aspect())
    inter, lo, hi = [], 0, n - 1
    while lo <= hi:
        inter.append(by_asp[hi])
        hi -= 1
        if lo <= hi:
            inter.append(by_asp[lo])
            lo += 1
    best, bs = None, 1e18
    for c in (seeded, list(auto), by_asp, by_asp[::-1], inter):
        s = ev(c)
        if s < bs:
            best, bs = list(c), s
    rnd, t0 = random.Random(7), time.perf_counter()
    while time.perf_counter() - t0 < budget:
        c = list(best)
        if rnd.random() < 0.5:
            i, j = rnd.sample(range(n), 2)
            c[i], c[j] = c[j], c[i]
        else:
            c.insert(rnd.randrange(n), c.pop(rnd.randrange(n)))
        s = ev(c)
        if s < bs - 1e-9:
            best, bs = c, s
    _SMART["key"], _SMART["order"] = key, list(best)
    return best


def optimize_rotations(pics, cfg):
    """One-shot: turn some images 90 degrees (aspect ratio untouched) when that
    gives a better A4 fit.  Images the user rotated by hand are left alone.
    The chosen turns are written into rot90.  Returns how many were turned."""
    auto = [p for p in pics if not p.free]
    for p in auto:                                   # bake current auto rotation
        p.rot90 = (p.rot90 + p.auto_rot) % 4
        p.auto_rot = 0
    if len(auto) < 2:
        return 0
    if cfg.smart:
        auto = smart_order(auto, cfg)

    def ev():
        return fit_score(auto, compute_layout(auto, cfg), cfg)

    ext = lambda p: max(p.aspect(), 1 / p.aspect())
    cands = sorted([p for p in auto if not p.lock_rot and ext(p) >= 1.3],
                   key=lambda p: -ext(p))
    best = ev()
    for _ in range(3):                               # repeat until nothing improves
        improved = False
        for p in cands:
            p.auto_rot ^= 1
            s = ev()
            if s < best - 0.03:
                best, improved = s, True
            else:
                p.auto_rot ^= 1
        if not improved:
            break
    n = 0
    for p in cands:
        if p.auto_rot:
            p.rot90, p.auto_rot, n = (p.rot90 + 1) % 4, 0, n + 1
    return n


def layout_all(pics, cfg):
    auto = [p for p in pics if not p.free]
    for p in auto:
        if not p.lock_rot:
            p.auto_rot = 0
    if cfg.smart:
        auto = smart_order(auto, cfg)
    cfg.order = auto                      # final on-page order (used by commit_order)
    n = compute_layout(auto, cfg)
    if cfg.autorot and len(auto) > 1:
        best = layout_score(auto, n)
        ext = lambda p: max(p.aspect(), 1 / p.aspect())
        cands = sorted([p for p in auto if not p.lock_rot and ext(p) >= 1.3],
                       key=lambda p: -ext(p))
        for p in cands:
            p.auto_rot = 1
            n2 = compute_layout(auto, cfg)
            s2 = layout_score(auto, n2)
            if s2 < best - 0.05:
                best, n = s2, n2
            else:
                p.auto_rot = 0
        n = compute_layout(auto, cfg)
    return n


# --------------------------------------------------------------------------
# graphics
# --------------------------------------------------------------------------
class PageItem(W_.QGraphicsItem):
    def __init__(self, index):
        super().__init__()
        self.index = index
        self.setZValue(-100)
        self.setPos(0, index * (A4_H + PAGE_GAP))

    def boundingRect(self):
        return QRectF(-2, -2, A4_W + 6, A4_H + 14)

    def paint(self, p, opt, widget=None):
        sc = self.scene()
        page = QRectF(0, 0, A4_W, A4_H)
        if not sc.exporting:
            p.fillRect(page.translated(1.2, 1.2), QColor(0, 0, 0, 70))
        p.fillRect(page, QColor(255, 255, 255))
        if sc.exporting:
            return
        if sc.cfg.guides:
            pen = QPen(QColor(150, 150, 150, 140))
            pen.setCosmetic(True)
            pen.setStyle(Qt.PenStyle.DashLine)
            p.setPen(pen)
            m = sc.cfg.margin
            p.drawRect(QRectF(m, m, A4_W - 2 * m, A4_H - 2 * m))
        f = p.font()
        f.setPointSizeF(4.2)
        p.setFont(f)
        p.setPen(QColor(215, 215, 215))
        p.drawText(QRectF(0, A4_H + 1.5, A4_W, 8), Qt.AlignmentFlag.AlignHCenter,
                   "Page %d" % (self.index + 1))
        if self.index == 0 and not sc.win.pics:
            f.setPointSizeF(7)
            p.setFont(f)
            p.setPen(QColor(150, 150, 150))
            p.drawText(page, Qt.AlignmentFlag.AlignCenter,
                       "Ctrl+V to paste an image\n(or copy images with\n'Auto-capture clipboard' on)")


class ImageItem(W_.QGraphicsItem):
    CORNERS = ((0, 0), (1, 0), (1, 1), (0, 1))

    def __init__(self, pic):
        super().__init__()
        self.pic = pic
        self.w = self.h = 10.0
        self.mode = None
        self.setFlag(W_.QGraphicsItem.GraphicsItemFlag.ItemIsSelectable, True)
        self.setAcceptedMouseButtons(Qt.MouseButton.LeftButton | Qt.MouseButton.RightButton)

    # geometry ----------------------------------------------------------
    def hsize(self):
        return 6.0 / max(0.3, self.scene().ppm) if self.scene() else 2.0

    def refresh(self, idx):
        x, y, w, h = self.pic.geom()
        self.prepareGeometryChange()
        self.w, self.h = w, h
        self.setPos(x, y)
        self.setTransformOriginPoint(w / 2, h / 2)
        self.setRotation(self.pic.fine if self.pic.free else 0.0)
        self.setScale(1.0)
        self.setOpacity(1.0)
        self.setZValue((1000 if self.pic.free else 0) + idx * 0.001 + self.pic.z)
        self.update()

    def boundingRect(self):
        pad = self.hsize() + 0.6
        return QRectF(-pad, -pad, self.w + 2 * pad, self.h + 2 * pad)

    def shape(self):
        path = QtGui.QPainterPath()
        path.addRect(QRectF(0, 0, self.w, self.h))
        if self.isSelected():
            hs = self.hsize()
            for cx, cy in self.CORNERS:
                path.addRect(QRectF(cx * self.w - hs, cy * self.h - hs, 2 * hs, 2 * hs))
        return path

    def itemChange(self, change, value):
        if change == W_.QGraphicsItem.GraphicsItemChange.ItemSelectedHasChanged:
            self.update()
        return super().itemChange(change, value)

    # painting ----------------------------------------------------------
    def paint(self, p, opt, widget=None):
        sc, pic, w, h = self.scene(), self.pic, self.w, self.h
        lod = opt.levelOfDetailFromTransform(p.worldTransform())
        c = pic.crop
        odd = pic.total_rot() % 2
        dw, dh = (h, w) if odd else (w, h)
        prev, full = pic.preview, pic.img
        use_full = prev is not full and dw * lod > (c[2] - c[0]) * prev.width() * 0.9
        img = full if use_full else prev
        iw, ih = img.width(), img.height()
        src = QRectF(c[0] * iw, c[1] * ih, (c[2] - c[0]) * iw, (c[3] - c[1]) * ih)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
        p.save()
        p.translate(w / 2, h / 2)
        p.rotate(90.0 * pic.total_rot())
        p.drawImage(QRectF(-dw / 2, -dh / 2, dw, dh), img, src)
        p.restore()
        if sc.cfg.border:
            pen = QPen(QColor(70, 70, 70))
            pen.setWidthF(0.2)
            p.setPen(pen)
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRect(QRectF(0, 0, w, h))
        if sc.exporting or not self.isSelected():
            return
        pen = QPen(ACCENT)
        pen.setCosmetic(True)
        pen.setWidth(2)
        if pic.free:
            pen.setStyle(Qt.PenStyle.DashLine)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRect(QRectF(0, 0, w, h))
        hs = self.hsize()
        p.setBrush(QBrush(QColor(255, 255, 255)))
        for cx, cy in self.CORNERS:
            p.drawRect(QRectF(cx * w - hs, cy * h - hs, 2 * hs, 2 * hs))

    # interaction -------------------------------------------------------
    def mousePressEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton:
            e.ignore()
            return
        sc = self.scene()
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            self.setSelected(not self.isSelected())
        elif not self.isSelected():
            sc.clearSelection()
            self.setSelected(True)
        self.mode, self.moved, self.k, self.undone = 'move', False, 1.0, False
        if self.isSelected() and len(sc.selectedItems()) == 1:
            hs = self.hsize() * 1.3
            for cx, cy in self.CORNERS:
                if (abs(e.pos().x() - cx * self.w) <= hs and abs(e.pos().y() - cy * self.h) <= hs):
                    self.mode = 'resize'
        self.p0, self.pos0 = e.scenePos(), self.pos()
        self.ctr = self.mapToScene(self.w / 2, self.h / 2)
        self.d0 = max(1e-3, math.hypot(self.p0.x() - self.ctr.x(), self.p0.y() - self.ctr.y()))
        self.r0 = list(self.pic.rect)
        e.accept()

    def mouseMoveEvent(self, e):
        if self.mode is None:
            return
        sc, pic = self.scene(), self.pic
        d = e.scenePos() - self.p0
        if self.mode == 'move':
            if not self.moved and (abs(d.x()) + abs(d.y())) * sc.ppm < 5:
                return
            if not self.moved:
                self.moved = True
                sc.win.push_undo()
                self.setZValue(5000)
                self.setOpacity(0.8)
            self.setPos(self.pos0 + d)
            if pic.free or (e.modifiers() & Qt.KeyboardModifier.ShiftModifier):
                sc.hint.hide()
            else:
                t = sc.win.drop_target(e.scenePos(), pic)
                if t:
                    best, before = t
                    x, y, w, h = best.cell
                    sc.hint.setRect(QRectF((x if before else x + w) - 0.7, y, 1.4, h))
                    sc.hint.show()
        elif self.mode == 'resize':
            dd = math.hypot(e.scenePos().x() - self.ctr.x(), e.scenePos().y() - self.ctr.y())
            self.k = max(0.2, dd / self.d0)
            if not self.undone:
                self.undone = True
                sc.win.push_undo()
            if pic.free:
                x, y, w, h = self.r0
                nw, nh = w * self.k, h * self.k
                pic.rect = [x + w / 2 - nw / 2, y + h / 2 - nh / 2, nw, nh]
                self.refresh(0)
                self.setZValue(5000)
            else:
                self.setScale(self.k)

    def mouseReleaseEvent(self, e):
        sc, pic, win = self.scene(), self.pic, self.scene().win
        sc.hint.hide()
        mode, self.mode = self.mode, None
        if mode == 'move' and self.moved:
            if pic.free:
                pic.rect[0], pic.rect[1] = self.pos().x(), self.pos().y()
                win.relayout()
            elif e.modifiers() & Qt.KeyboardModifier.ShiftModifier:
                pic.free = True
                pic.rect = [self.pos().x(), self.pos().y(), self.w, self.h]
                win.relayout()
            else:
                win.reorder_to(pic, e.scenePos())
        elif mode == 'resize' and abs(self.k - 1) > 1e-3:
            if not pic.free:
                pic.weight = min(4.0, max(0.25, pic.weight * self.k))
            win.relayout()
        e.accept()

    def mouseDoubleClickEvent(self, e):
        self.scene().win.crop_selected()

    def contextMenuEvent(self, e):
        sc = self.scene()
        if not self.isSelected():
            sc.clearSelection()
            self.setSelected(True)
        sc.win.item_menu.exec(e.screenPos())
        e.accept()


class CollageScene(W_.QGraphicsScene):
    def __init__(self, win):
        super().__init__()
        self.win, self.cfg = win, win.cfg
        self.exporting = False
        self.ppm = 3.0
        self.pages, self.items_by_pic = [], {}
        self.hint = W_.QGraphicsRectItem()
        self.hint.setBrush(QBrush(ACCENT))
        self.hint.setPen(QPen(Qt.PenStyle.NoPen))
        self.hint.setZValue(6000)
        self.hint.hide()
        self.addItem(self.hint)

    def set_ppm(self, v):
        self.ppm = v
        for it in self.items_by_pic.values():
            it.prepareGeometryChange()
            it.update()

    def sync(self, pics, npages):
        while len(self.pages) < npages:
            pg = PageItem(len(self.pages))
            self.addItem(pg)
            self.pages.append(pg)
        while len(self.pages) > npages:
            self.removeItem(self.pages.pop())
        live = set(pics)
        for pic in [p for p in self.items_by_pic if p not in live]:
            self.removeItem(self.items_by_pic.pop(pic))
        for idx, pic in enumerate(pics):
            it = self.items_by_pic.get(pic)
            if it is None:
                it = self.items_by_pic[pic] = ImageItem(pic)
                self.addItem(it)
            it.refresh(idx)
        self.setSceneRect(-14, -14, A4_W + 28, npages * (A4_H + PAGE_GAP) + 8)
        self.update()


class CollageView(W_.QGraphicsView):
    def __init__(self, scene, win):
        super().__init__(scene)
        self.win, self.fit_mode, self._pan = win, True, None
        self.setRenderHints(QPainter.RenderHint.Antialiasing |
                            QPainter.RenderHint.SmoothPixmapTransform)
        self.setDragMode(W_.QGraphicsView.DragMode.RubberBandDrag)
        self.setTransformationAnchor(W_.QGraphicsView.ViewportAnchor.AnchorUnderMouse)
        self.setBackgroundBrush(QBrush(QColor(84, 86, 92)))
        self.setAcceptDrops(True)
        self.viewport().setAcceptDrops(True)

    def _scaled(self):
        self.scene().set_ppm(self.transform().m11())

    def zoom(self, f):
        self.fit_mode = False
        cur = self.transform().m11()
        f = min(25.0, max(0.8, cur * f)) / cur
        self.scale(f, f)
        self._scaled()

    def fit_width(self):
        self.fit_mode = True
        ppm = max(0.8, (self.viewport().width() - 30) / (A4_W + 8))
        self.resetTransform()
        self.scale(ppm, ppm)
        self._scaled()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.fit_mode:
            self.fit_width()

    def wheelEvent(self, e):
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            self.zoom(1.0015 ** e.angleDelta().y())
            e.accept()
        else:
            super().wheelEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.MiddleButton:
            self._pan = e.position()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
            e.accept()
            return
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._pan is not None:
            d = e.position() - self._pan
            self._pan = e.position()
            self.horizontalScrollBar().setValue(int(self.horizontalScrollBar().value() - d.x()))
            self.verticalScrollBar().setValue(int(self.verticalScrollBar().value() - d.y()))
            e.accept()
            return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        if self._pan is not None and e.button() == Qt.MouseButton.MiddleButton:
            self._pan = None
            self.unsetCursor()
            e.accept()
            return
        super().mouseReleaseEvent(e)

    def _ok(self, md):
        return md.hasImage() or md.hasUrls()

    def dragEnterEvent(self, e):
        e.acceptProposedAction() if self._ok(e.mimeData()) else e.ignore()

    def dragMoveEvent(self, e):
        e.acceptProposedAction() if self._ok(e.mimeData()) else e.ignore()

    def dropEvent(self, e):
        if self.win.add_from_mime(e.mimeData()):
            e.acceptProposedAction()


# --------------------------------------------------------------------------
# crop dialog
# --------------------------------------------------------------------------
class CropCanvas(W_.QWidget):
    MIN = 0.04

    def __init__(self, img, crop):
        super().__init__()
        self.img, self.c, self.drag = img, list(crop), None
        self.setMinimumSize(680, 480)
        self.setMouseTracking(True)

    def target(self):
        s = min((self.width() - 24) / self.img.width(), (self.height() - 24) / self.img.height())
        w, h = self.img.width() * s, self.img.height() * s
        return QRectF((self.width() - w) / 2, (self.height() - h) / 2, w, h)

    def crop_rect(self):
        t, c = self.target(), self.c
        return QRectF(t.x() + c[0] * t.width(), t.y() + c[1] * t.height(),
                      (c[2] - c[0]) * t.width(), (c[3] - c[1]) * t.height())

    def handles(self):
        r = self.crop_rect()
        cx, cy = r.center().x(), r.center().y()
        return {'tl': QPointF(r.left(), r.top()), 'tr': QPointF(r.right(), r.top()),
                'br': QPointF(r.right(), r.bottom()), 'bl': QPointF(r.left(), r.bottom()),
                't': QPointF(cx, r.top()), 'b': QPointF(cx, r.bottom()),
                'l': QPointF(r.left(), cy), 'r': QPointF(r.right(), cy)}

    def hit(self, pos):
        for name, pt in self.handles().items():
            if abs(pos.x() - pt.x()) <= 10 and abs(pos.y() - pt.y()) <= 10:
                return name
        return 'move' if self.crop_rect().contains(pos) else None

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.fillRect(self.rect(), QColor(50, 52, 56))
        t, r = self.target(), self.crop_rect()
        p.drawImage(t, self.img)
        shade = QColor(0, 0, 0, 150)
        p.fillRect(QRectF(t.left(), t.top(), t.width(), r.top() - t.top()), shade)
        p.fillRect(QRectF(t.left(), r.bottom(), t.width(), t.bottom() - r.bottom()), shade)
        p.fillRect(QRectF(t.left(), r.top(), r.left() - t.left(), r.height()), shade)
        p.fillRect(QRectF(r.right(), r.top(), t.right() - r.right(), r.height()), shade)
        p.setPen(QPen(ACCENT, 2))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRect(r)
        p.setBrush(QBrush(QColor(255, 255, 255)))
        for pt in self.handles().values():
            p.drawRect(QRectF(pt.x() - 5, pt.y() - 5, 10, 10))

    def mousePressEvent(self, e):
        h = self.hit(e.position())
        if h:
            self.drag = (h, e.position(), list(self.c))

    def mouseMoveEvent(self, e):
        if not self.drag:
            h = self.hit(e.position())
            cur = {'move': Qt.CursorShape.SizeAllCursor, 'tl': Qt.CursorShape.SizeFDiagCursor,
                   'br': Qt.CursorShape.SizeFDiagCursor, 'tr': Qt.CursorShape.SizeBDiagCursor,
                   'bl': Qt.CursorShape.SizeBDiagCursor, 't': Qt.CursorShape.SizeVerCursor,
                   'b': Qt.CursorShape.SizeVerCursor, 'l': Qt.CursorShape.SizeHorCursor,
                   'r': Qt.CursorShape.SizeHorCursor}.get(h, Qt.CursorShape.ArrowCursor)
            self.setCursor(cur)
            return
        mode, p0, c0 = self.drag
        t = self.target()
        dx = (e.position().x() - p0.x()) / t.width()
        dy = (e.position().y() - p0.y()) / t.height()
        cl = lambda v, a, b: min(b, max(a, v))
        c, M = list(c0), self.MIN
        if mode == 'move':
            w, h = c0[2] - c0[0], c0[3] - c0[1]
            nx, ny = cl(c0[0] + dx, 0, 1 - w), cl(c0[1] + dy, 0, 1 - h)
            c = [nx, ny, nx + w, ny + h]
        else:
            if 'l' in mode: c[0] = cl(c0[0] + dx, 0, c0[2] - M)
            if 'r' in mode: c[2] = cl(c0[2] + dx, c0[0] + M, 1)
            if 't' in mode: c[1] = cl(c0[1] + dy, 0, c0[3] - M)
            if 'b' in mode: c[3] = cl(c0[3] + dy, c0[1] + M, 1)
        self.c = c
        self.update()

    def mouseReleaseEvent(self, e):
        self.drag = None


class CropDialog(W_.QDialog):
    def __init__(self, pic, parent):
        super().__init__(parent)
        self.setWindowTitle("Crop (original orientation) - drag edges to cut ads / watermarks")
        self.canvas = CropCanvas(pic.preview, pic.crop)
        lay = W_.QVBoxLayout(self)
        lay.addWidget(self.canvas, 1)
        row = W_.QHBoxLayout()
        reset = W_.QPushButton("Reset")
        reset.clicked.connect(self._reset)
        ok, cancel = W_.QPushButton("Apply"), W_.QPushButton("Cancel")
        ok.setDefault(True)
        ok.clicked.connect(self.accept)
        cancel.clicked.connect(self.reject)
        row.addWidget(reset)
        row.addStretch(1)
        row.addWidget(cancel)
        row.addWidget(ok)
        lay.addLayout(row)

    def _reset(self):
        self.canvas.c = [0.0, 0.0, 1.0, 1.0]
        self.canvas.update()


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def prepare_image(im):
    if im.hasAlphaChannel():                     # flatten onto white paper
        flat = QImage(im.size(), QImage.Format.Format_RGB32)
        flat.fill(QColor(255, 255, 255))
        q = QPainter(flat)
        q.drawImage(0, 0, im)
        q.end()
        im = flat
    elif im.format() != QImage.Format.Format_RGB32:
        im = im.convertToFormat(QImage.Format.Format_RGB32)
    if max(im.width(), im.height()) > MAX_SIDE:
        im = im.scaled(MAX_SIDE, MAX_SIDE, Qt.AspectRatioMode.KeepAspectRatio,
                       Qt.TransformationMode.SmoothTransformation)
    return im


def image_sig(im):
    small = im.scaled(16, 16, Qt.AspectRatioMode.IgnoreAspectRatio,
                      Qt.TransformationMode.FastTransformation)
    ba = QtCore.QByteArray()
    buf = QtCore.QBuffer(ba)
    buf.open(QtCore.QIODevice.OpenModeFlag.WriteOnly)
    small.save(buf, "BMP")
    buf.close()
    return (im.width(), im.height(), hashlib.md5(bytes(ba.data())).hexdigest())


def jpeg_bytes(im, q=95):
    ba = QtCore.QByteArray()
    buf = QtCore.QBuffer(ba)
    buf.open(QtCore.QIODevice.OpenModeFlag.WriteOnly)
    im.save(buf, "JPEG", q)
    buf.close()
    return bytes(ba.data())


# --------------------------------------------------------------------------
# main window
# --------------------------------------------------------------------------
class MainWindow(W_.QMainWindow):
    def __init__(self):
        super().__init__()
        self.pics, self.undo_stack, self.path = [], [], None
        self.cfg = Cfg()
        self.scene = CollageScene(self)
        self.view = CollageView(self.scene, self)
        self.setCentralWidget(self.view)
        self.clip = W_.QApplication.clipboard()
        self.auto_capture, self._selfclip, self._last_sig = False, False, None
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self.relayout)
        self.clip.dataChanged.connect(self._clip_changed)
        self._build_ui()
        self.relayout()
        self.setWindowTitle("Collage Notes")

    # ---- ui --------------------------------------------------------------
    def act(self, text, key, slot, checkable=False, checked=False):
        a = QAction(text, self)
        if key:
            a.setShortcuts([QKeySequence(k) for k in key.split('|')])
        if checkable:
            a.setCheckable(True)
            a.setChecked(checked)
            a.toggled.connect(slot)
        else:
            a.triggered.connect(lambda *_: slot())
        self.addAction(a)
        return a

    def _build_ui(self):
        A = self.act
        a_open, a_save = A("Open...", "Ctrl+O", self.open_project), A("Save", "Ctrl+S", self.save_project)
        a_saveas = A("Save as...", "Ctrl+Shift+S", lambda: self.save_project(True))
        a_pdf, a_print = A("Export PDF...", "Ctrl+E", self.export_pdf), A("Print...", "Ctrl+P", self.print_pages)
        a_copy = A("Copy page to clipboard", "Ctrl+Shift+C", self.copy_page)
        a_quit = A("Quit", "Ctrl+Q", self.close)
        a_paste = A("Paste image", "Ctrl+V|Shift+Ins", self.paste)
        a_undo, a_del = A("Undo", "Ctrl+Z", self.do_undo), A("Delete", "Del", self.delete_selected)
        a_all, a_unfloat = A("Select all", "Ctrl+A", self.select_all), A("Return all floating to flow", "", self.unfloat_all)
        a_cw, a_ccw = A("Rotate right", "R", lambda: self.rotate(1)), A("Rotate left", "Shift+R", lambda: self.rotate(-1))
        a_autorot = A("Auto-rotate images to fit (once)", "Ctrl+Shift+R", self.auto_rotate_now)
        a_crop = A("Crop...", "C", self.crop_selected)
        a_big, a_small = A("Bigger", "+|=", lambda: self.scale_sel(1.15)), A("Smaller", "-", lambda: self.scale_sel(1 / 1.15))
        a_float = A("Float / back to flow", "F", self.toggle_float)
        a_prev, a_next = A("Move earlier", "Ctrl+Left", lambda: self.move_order(-1)), A("Move later", "Ctrl+Right", lambda: self.move_order(1))
        a_front, a_back = A("Bring to front", "]", lambda: self.zorder(True)), A("Send to back", "[", lambda: self.zorder(False))
        a_tr, a_tl = A("Tilt right 5\u00b0", ".", lambda: self.tilt(5)), A("Tilt left 5\u00b0", ",", lambda: self.tilt(-5))
        a_zi, a_zo = A("Zoom in", "Ctrl++|Ctrl+=", lambda: self.view.zoom(1.25)), A("Zoom out", "Ctrl+-", lambda: self.view.zoom(0.8))
        a_fit = A("Fit page width", "Ctrl+0", self.view.fit_width)
        a_cap = A("Auto-capture clipboard", "", self.set_capture, True, False)
        a_fr = A("Frames around images", "", lambda v: self._cfg_set('border', v), True, True)
        a_gd = A("Margin guides", "", lambda v: self._cfg_set('guides', v), True, True)

        mb = self.menuBar()
        m = mb.addMenu("&File")
        for a in (a_open, a_save, a_saveas, None, a_pdf, a_print, a_copy, None, a_quit):
            m.addAction(a) if a else m.addSeparator()
        m = mb.addMenu("&Edit")
        for a in (a_paste, a_undo, a_del, a_all, None, a_unfloat):
            m.addAction(a) if a else m.addSeparator()
        m = mb.addMenu("&Image")
        for a in (a_cw, a_ccw, a_autorot, a_crop, None, a_big, a_small, None, a_float, a_prev, a_next, None,
                  a_front, a_back, a_tr, a_tl):
            m.addAction(a) if a else m.addSeparator()
        m = mb.addMenu("&View")
        for a in (a_zi, a_zo, a_fit, None, a_cap, a_fr, a_gd):
            m.addAction(a) if a else m.addSeparator()

        self.item_menu = W_.QMenu(self)
        for a in (a_crop, a_cw, a_ccw, None, a_big, a_small, None, a_float, a_prev, a_next, a_front, a_back, None, a_del):
            self.item_menu.addAction(a) if a else self.item_menu.addSeparator()

        tb = self.addToolBar("main")
        tb.setMovable(False)
        for a in (a_paste, a_cw, a_autorot, a_crop, a_big, a_small, a_float, a_del, a_undo, None, a_pdf, a_copy, None, a_cap):
            tb.addAction(a) if a else tb.addSeparator()

        dock = W_.QDockWidget("Layout", self)
        dock.setFeatures(W_.QDockWidget.DockWidgetFeature.NoDockWidgetFeatures)
        box = W_.QWidget()
        lay = W_.QVBoxLayout(box)
        self._slider(lay, "Rows per page", 20, 80, int(self.cfg.rows * 10), lambda v: v / 10.0, "rows", "{:.1f}",
                     "Fewer rows = bigger pictures, more rows = smaller")
        self._slider(lay, "Gap (mm)", -60, 100, int(self.cfg.gap * 10), lambda v: v / 10.0, "gap", "{:.1f}",
                     "Negative values make neighbours overlap")
        self._slider(lay, "Page margin (mm)", 30, 250, int(self.cfg.margin * 10), lambda v: v / 10.0, "margin", "{:.1f}")
        self.cb_smart = W_.QCheckBox("Smart order (ignore paste order)")
        self.cb_smart.setToolTip("Rearrange all images automatically for the best A4 fit:\n"
                                 "nothing too tiny, nothing too big. Dragging an image turns this off.")
        self.cb_smart.setChecked(self.cfg.smart)
        self.cb_smart.toggled.connect(lambda v: self._cfg_set('smart', v))
        lay.addWidget(self.cb_smart)
        cb = W_.QCheckBox("Auto-rotate to fit")
        cb.setToolTip("Turn awkward tall/wide images 90\u00b0 when that packs the pages better")
        cb.toggled.connect(lambda v: self._cfg_set('autorot', v))
        lay.addWidget(cb)
        btn = W_.QPushButton("Auto-rotate images now")
        btn.setToolTip("Click once after adding all images: turns some of them 90\u00b0 "
                       "(aspect ratio kept) when that fits the pages better.\n"
                       "Images you rotated yourself are left alone. Ctrl+Z undoes it.")
        btn.clicked.connect(self.auto_rotate_now)
        lay.addWidget(btn)
        hint = W_.QLabel("<b>Drag</b>: reorder<br><b>Shift+drag</b>: float / overlap<br>"
                         "<b>Corner drag</b>: resize<br><b>Double-click</b>: crop<br>"
                         "<b>R</b> rotate \u00b7 <b>F</b> float \u00b7 <b>+/-</b> size<br>"
                         "<b>Ctrl+wheel</b>: zoom \u00b7 middle-drag: pan")
        hint.setStyleSheet("color: gray")
        lay.addSpacing(10)
        lay.addWidget(hint)
        lay.addStretch(1)
        box.setMinimumWidth(190)
        dock.setWidget(box)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea, dock)
        self.status = W_.QLabel()
        self.statusBar().addPermanentWidget(self.status)

    def _slider(self, lay, title, lo, hi, val, conv, attr, fmt, tip=""):
        lab = W_.QLabel()
        s = W_.QSlider(Qt.Orientation.Horizontal)
        s.setRange(lo, hi)
        s.setValue(val)
        s.setToolTip(tip)

        def upd(v):
            lab.setText("%s: %s" % (title, fmt.format(conv(v))))
            setattr(self.cfg, attr, conv(v))
            self._timer.start(40)
        s.valueChanged.connect(upd)
        upd(val)
        lay.addWidget(lab)
        lay.addWidget(s)

    def _cfg_set(self, attr, v):
        setattr(self.cfg, attr, v)
        self._timer.start(10)

    # ---- model plumbing ---------------------------------------------------
    def selected_pics(self):
        sel = {it.pic for it in self.scene.selectedItems() if isinstance(it, ImageItem)}
        return [p for p in self.pics if p in sel]

    def push_undo(self):
        self.undo_stack.append([(p, p.state()) for p in self.pics])
        del self.undo_stack[:-60]

    def do_undo(self):
        if not self.undo_stack:
            return
        snap = self.undo_stack.pop()
        self.pics = [p for p, _ in snap]
        for p, s in snap:
            p.set_state(s)
        self.relayout()

    def relayout(self):
        n = layout_all(self.pics, self.cfg)
        pitch = A4_H + PAGE_GAP
        for p in self.pics:
            if p.free:
                n = max(n, int(max(0, p.rect[1] + p.rect[3] / 2) // pitch) + 1)
        self.scene.sync(self.pics, n)
        self.status.setText("%d images \u00b7 %d page%s" % (len(self.pics), n, "" if n == 1 else "s"))

    def each_selected(self, fn):
        sel = self.selected_pics()
        if not sel:
            return
        self.push_undo()
        for p in sel:
            fn(p)
        self.relayout()

    # ---- actions ------------------------------------------------------------
    def rotate(self, d):
        def f(p):
            p.rot90 = (p.rot90 + p.auto_rot + d) % 4
            p.auto_rot, p.lock_rot = 0, True
            if p.free:
                p.refit_free()
        self.each_selected(f)

    def scale_sel(self, k):
        def f(p):
            if p.free:
                x, y, w, h = p.rect
                p.rect = [x + w / 2 - w * k / 2, y + h / 2 - h * k / 2, w * k, h * k]
            else:
                p.weight = min(4.0, max(0.25, p.weight * k))
        self.each_selected(f)

    def toggle_float(self):
        def f(p):
            if p.free:
                p.free = False
            else:
                p.rect = list(p.geom())
                p.free = True
        self.each_selected(f)

    def tilt(self, d):
        def f(p):
            if not p.free:
                p.rect, p.free = list(p.geom()), True
            p.fine = (p.fine + d) % 360
        self.each_selected(f)

    def zorder(self, front):
        def f(p):
            zs = [q.z for q in self.pics]
            p.z = (max(zs) + 1) if front else (min(zs) - 1)
        self.each_selected(f)

    def auto_rotate_now(self):
        if len([p for p in self.pics if not p.free]) < 2:
            return
        self.push_undo()
        n = optimize_rotations(self.pics, self.cfg)
        if n == 0:
            self.undo_stack.pop()
        self.relayout()
        self.statusBar().showMessage(
            "Rotated %d image%s to fit better (Ctrl+Z to undo)" % (n, "" if n == 1 else "s") if n
            else "Layout is already a good fit - nothing rotated", 5000)

    def commit_order(self):
        """Make the current on-screen order the real order, then stop auto-ordering."""
        if not self.cfg.smart:
            return
        order = getattr(self.cfg, "order", None)
        slots = [i for i, p in enumerate(self.pics) if not p.free]
        if order and len(order) == len(slots):
            for i, p in zip(slots, order):
                self.pics[i] = p
        self.cb_smart.blockSignals(True)
        self.cb_smart.setChecked(False)
        self.cb_smart.blockSignals(False)
        self.cfg.smart = False

    def move_order(self, d):
        self.commit_order()
        sel = self.selected_pics()
        if len(sel) != 1:
            return
        p = sel[0]
        i = self.pics.index(p)
        j = i + d
        while 0 <= j < len(self.pics) and self.pics[j].free:
            j += d
        if 0 <= j < len(self.pics):
            self.push_undo()
            self.pics[i], self.pics[j] = self.pics[j], self.pics[i]
            self.relayout()

    def delete_selected(self):
        sel = self.selected_pics()
        if sel:
            self.push_undo()
            self.pics = [p for p in self.pics if p not in sel]
            self.relayout()

    def select_all(self):
        for it in self.scene.items_by_pic.values():
            it.setSelected(True)

    def unfloat_all(self):
        if any(p.free for p in self.pics):
            self.push_undo()
            for p in self.pics:
                p.free = False
            self.relayout()

    def crop_selected(self):
        sel = self.selected_pics()
        if len(sel) != 1:
            return
        p = sel[0]
        dlg = CropDialog(p, self)
        if dlg.exec():
            self.push_undo()
            p.crop = [min(1, max(0, v)) for v in dlg.canvas.c]
            if p.free:
                p.refit_free()
            self.relayout()

    def drop_target(self, pt, exclude):
        auto = [q for q in self.pics if not q.free and q is not exclude and q.cell]
        if not auto:
            return None
        def d2(q):
            x, y, w, h = q.cell
            return (pt.x() - (x + w / 2)) ** 2 + (pt.y() - (y + h / 2)) ** 2
        best = min(auto, key=d2)
        x, y, w, h = best.cell
        before = pt.x() < x + w / 2 if abs(pt.y() - (y + h / 2)) < h / 2 else pt.y() < y + h / 2
        return best, before

    def reorder_to(self, pic, pt):
        self.commit_order()
        t = self.drop_target(pt, pic)
        if t:
            best, before = t
            self.pics.remove(pic)
            i = self.pics.index(best)
            self.pics.insert(i if before else i + 1, pic)
        self.relayout()

    # ---- clipboard ----------------------------------------------------------
    def add_images(self, imgs):
        imgs = [prepare_image(i) for i in imgs if not i.isNull()]
        if not imgs:
            return False
        self.push_undo()
        new = [Pic(i) for i in imgs]
        self.pics.extend(new)
        self.relayout()
        self.scene.clearSelection()
        it = self.scene.items_by_pic[new[-1]]
        it.setSelected(True)
        self.view.ensureVisible(it, 30, 30)
        return True

    def add_from_mime(self, md):
        imgs = []
        if md.hasUrls():
            for u in md.urls():
                if u.isLocalFile():
                    im = QImage(u.toLocalFile())
                    if not im.isNull():
                        imgs.append(im)
        if not imgs and md.hasImage():
            im = self.clip.image() if md is self.clip.mimeData() else QImage(md.imageData())
            if not im.isNull():
                imgs.append(im)
        return self.add_images(imgs)

    def paste(self):
        if not self.add_from_mime(self.clip.mimeData()):
            self.statusBar().showMessage("No image in the clipboard", 3000)

    def set_capture(self, on):
        self.auto_capture = on
        self._last_sig = None
        self.statusBar().showMessage(
            "Auto-capture ON - copy images anywhere (Wayland: window must be focused)" if on
            else "Auto-capture off", 4000)

    def _clip_changed(self):
        if self.auto_capture and not self._selfclip:
            QTimer.singleShot(60, self._grab_clip)

    def _grab_clip(self):
        md = self.clip.mimeData()
        if not md or not md.hasImage():
            return
        im = self.clip.image()
        if im.isNull():
            return
        sig = image_sig(im)
        if sig != self._last_sig:
            self._last_sig = sig
            self.add_images([im])

    # ---- output ---------------------------------------------------------------
    def render_pages(self, dev, painter_setup=None):
        sc = self.scene
        sc.exporting = True
        sc.clearSelection()
        p = QPainter(dev)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        for k in range(len(sc.pages)):
            if k:
                dev.newPage()
            sc.render(p, QRectF(0, 0, dev.width(), dev.height()),
                      QRectF(0, k * (A4_H + PAGE_GAP), A4_W, A4_H),
                      Qt.AspectRatioMode.IgnoreAspectRatio)
        p.end()
        sc.exporting = False
        sc.update()

    def export_pdf(self, path=None):
        if not path:
            path, _ = W_.QFileDialog.getSaveFileName(self, "Export PDF", "notes.pdf", "PDF (*.pdf)")
        if not path:
            return
        w = QtGui.QPdfWriter(path)
        w.setPageSize(QtGui.QPageSize(QtGui.QPageSize.PageSizeId.A4))
        w.setResolution(300)
        w.setPageMargins(QtCore.QMarginsF(0, 0, 0, 0))
        w.setTitle("Collage notes")
        self.render_pages(w)
        self.statusBar().showMessage("Saved " + path, 5000)

    def print_pages(self):
        pr = QtPrintSupport.QPrinter(QtPrintSupport.QPrinter.PrinterMode.HighResolution)
        pr.setPageSize(QtGui.QPageSize(QtGui.QPageSize.PageSizeId.A4))
        pr.setResolution(300)
        if QtPrintSupport.QPrintDialog(pr, self).exec():
            self.render_pages(pr)

    def copy_page(self):
        n = len(self.scene.pages)
        c = self.view.mapToScene(self.view.viewport().rect().center())
        k = min(n - 1, max(0, int(c.y() // (A4_H + PAGE_GAP))))
        im = QImage(1654, 2339, QImage.Format.Format_RGB32)
        im.fill(QColor(255, 255, 255))
        sc = self.scene
        sc.exporting = True
        sc.clearSelection()
        p = QPainter(im)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        sc.render(p, QRectF(0, 0, im.width(), im.height()),
                  QRectF(0, k * (A4_H + PAGE_GAP), A4_W, A4_H), Qt.AspectRatioMode.IgnoreAspectRatio)
        p.end()
        sc.exporting = False
        sc.update()
        self._selfclip = True
        self.clip.setImage(im)
        QTimer.singleShot(800, lambda: setattr(self, '_selfclip', False))
        self.statusBar().showMessage("Page %d copied to clipboard" % (k + 1), 4000)

    # ---- project files -----------------------------------------------------------
    def save_project(self, as_new=False, path=None):
        path = path or (None if as_new else self.path)
        if not path:
            path, _ = W_.QFileDialog.getSaveFileName(self, "Save", "notes.collage", "Collage (*.collage)")
        if not path:
            return
        meta = dict(version=1, cfg=dict(rows=self.cfg.rows, gap=self.cfg.gap, margin=self.cfg.margin,
                                        autorot=self.cfg.autorot, border=self.cfg.border), pics=[])
        with zipfile.ZipFile(path, 'w', zipfile.ZIP_STORED) as z:
            for i, p in enumerate(self.pics):
                name = "img%03d.jpg" % i
                z.writestr(name, jpeg_bytes(p.img))
                d = p.state()
                d['file'] = name
                meta['pics'].append(d)
            z.writestr("project.json", json.dumps(meta))
        self.path = path
        self.statusBar().showMessage("Saved " + path, 4000)

    def open_project(self, path=None):
        if not path:
            path, _ = W_.QFileDialog.getOpenFileName(self, "Open", "", "Collage (*.collage)")
        if not path:
            return
        with zipfile.ZipFile(path) as z:
            meta = json.loads(z.read("project.json"))
            pics = []
            for d in meta['pics']:
                im = QImage.fromData(z.read(d.pop('file')))
                pic = Pic(im)
                pic.set_state(d)
                pics.append(pic)
        for k, v in meta.get('cfg', {}).items():
            setattr(self.cfg, k, v)
        self.pics, self.undo_stack, self.path = pics, [], path
        self.relayout()


def main():
    app = W_.QApplication(sys.argv)
    app.setApplicationName("collage-notes")
    QtGui.QGuiApplication.setDesktopFileName("collage-notes")   # Wayland app_id
    win = MainWindow()
    win.resize(1180, 860)
    win.show()
    imgs = []
    for a in sys.argv[1:]:
        if a.endswith(".collage"):
            win.open_project(a)
        else:
            im = QImage(a)
            if not im.isNull():
                imgs.append(im)
    if imgs:
        win.add_images(imgs)
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
