/* ============================================================================
   viz.js — interactive geometric visualisations for MATH2014 Linear Algebra.
   Vanilla JS, canvas 2D. Mounts any <figure class="viz" data-viz="NAME">.
   Geometry-first, in the spirit of 3Blue1Brown: transformations warp the
   grid, determinants are areas, eigenvectors are the lines that don't turn.
   ============================================================================ */
(function () {
  'use strict';

  /* ---------- small math helpers ---------- */
  var TAU = Math.PI * 2;
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function easeInOut(t) { return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2; }
  function fmt(x, d) { d = d == null ? 2 : d; var s = (Math.abs(x) < 1e-9 ? 0 : x).toFixed(d); return s === '-0' || s === '-0.00' || s === '-0.0' ? s.replace('-', '') : s; }
  // matrix as {a,b,c,d}: columns are i-hat=(a,c), j-hat=(b,d)
  function apply(M, x, y) { return [M.a * x + M.b * y, M.c * x + M.d * y]; }
  function det(M) { return M.a * M.d - M.b * M.c; }
  function inv(M) { var D = det(M); if (Math.abs(D) < 1e-9) return null; return { a: M.d / D, b: -M.b / D, c: -M.c / D, d: M.a / D }; }
  function mul(M, N) { return { a: M.a * N.a + M.b * N.c, b: M.a * N.b + M.b * N.d, c: M.c * N.a + M.d * N.c, d: M.c * N.b + M.d * N.d }; }
  function lerpM(A, B, t) { return { a: lerp(A.a, B.a, t), b: lerp(A.b, B.b, t), c: lerp(A.c, B.c, t), d: lerp(A.d, B.d, t) }; }
  var I2 = { a: 1, b: 0, c: 0, d: 1 };
  // real eigenstuff of 2x2 {a,b,c,d}
  function eigen(M) {
    var T = M.a + M.d, D = det(M), disc = T * T - 4 * D;
    if (disc < -1e-9) return { real: false };
    disc = Math.sqrt(Math.max(0, disc));
    var l1 = (T + disc) / 2, l2 = (T - disc) / 2;
    function vec(l) {
      // (A - lI) v = 0
      var a = M.a - l, b = M.b, c = M.c, d = M.d - l, v;
      if (Math.abs(b) > 1e-6 || Math.abs(a) > 1e-6) v = [b, -a] ;        // row1: a*x+b*y=0 -> (b,-a)
      else if (Math.abs(d) > 1e-6 || Math.abs(c) > 1e-6) v = [d, -c];    // row2: c*x+d*y=0 -> (d,-c)
      else v = [1, 0];
      var n = Math.hypot(v[0], v[1]); if (n < 1e-9) { v = [1, 0]; n = 1; }
      return [v[0] / n, v[1] / n];
    }
    return { real: true, l1: l1, l2: l2, v1: vec(l1), v2: vec(l2), repeated: Math.abs(l1 - l2) < 1e-6 };
  }

  /* ---------- theme-aware palette ---------- */
  function palette() {
    var cs = getComputedStyle(document.documentElement);
    function c(n, fb) { var v = cs.getPropertyValue(n).trim(); return v || fb; }
    var dark = document.documentElement.getAttribute('data-theme') === 'dark';
    return {
      ink: c('--ink', '#17202e'), muted: c('--muted', '#53617a'),
      surface: c('--surface', '#fff'), line: c('--line', '#ccd5e4'),
      accent: c('--accent', '#1b3a7a'), hot: c('--hot', '#d97706'),
      ok: c('--ok', '#1f7a4d'), bad: c('--bad', '#b42334'), info: c('--info', '#1b62b0'),
      grid: dark ? 'rgba(150,170,200,.16)' : 'rgba(70,90,130,.14)',
      gridWarp: dark ? 'rgba(123,162,232,.55)' : 'rgba(27,58,122,.42)',
      fillWarp: dark ? 'rgba(123,162,232,.09)' : 'rgba(27,58,122,.07)',
      ihat: c('--ok', '#1f7a4d'), jhat: c('--bad', '#b42334'),
      ghost: dark ? 'rgba(157,171,190,.4)' : 'rgba(83,97,122,.4)',
      dark: dark
    };
  }

  /* ---------- Scene2D: canvas + world coordinates ---------- */
  function Scene(stage, opts) {
    opts = opts || {};
    this.stage = stage;
    this.canvas = document.createElement('canvas');
    this.canvas.className = 'viz-canvas';
    stage.appendChild(this.canvas);
    this.ctx = this.canvas.getContext('2d');
    this.H = opts.height || 380;
    this.range = opts.range || 5;      // half-height in world units
    this.gridN = opts.gridN || 9;      // integer extent drawn
    this.panx = opts.panx || 0;        // world units to shift origin right
    this.pal = palette();
    this.render = opts.render || function () {};
    var self = this;
    this._raf = 0;
    this.resize();
    this._ro = ('ResizeObserver' in window) ? new ResizeObserver(function () { self.resize(); self.requestDraw(); }) : null;
    if (this._ro) this._ro.observe(stage);
    this._mo = new MutationObserver(function () { self.pal = palette(); self.requestDraw(); });
    this._mo.observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  }
  Scene.prototype.resize = function () {
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var w = this.stage.clientWidth || 600;
    this.W = w;
    this.canvas.style.width = w + 'px';
    this.canvas.style.height = this.H + 'px';
    this.canvas.width = Math.round(w * dpr);
    this.canvas.height = Math.round(this.H * dpr);
    this.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    this.unit = Math.min(w, this.H) / (2 * this.range);
    this.cx = w / 2 + this.panx * this.unit;
    this.cy = this.H / 2;
  };
  Scene.prototype.S = function (x, y) { return [this.cx + x * this.unit, this.cy - y * this.unit]; };     // world->screen
  Scene.prototype.W2 = function (px, py) { return [(px - this.cx) / this.unit, (this.cy - py) / this.unit]; }; // screen->world
  Scene.prototype.requestDraw = function () {
    var self = this; if (this._raf) return;
    this._raf = requestAnimationFrame(function () { self._raf = 0; self.render(self); });
  };
  Scene.prototype.clear = function () {
    var ctx = this.ctx; ctx.clearRect(0, 0, this.W, this.H);
  };
  Scene.prototype.bgGrid = function () {
    var ctx = this.ctx, R = this.gridN, i, p0, p1;
    ctx.lineWidth = 1; ctx.strokeStyle = this.pal.grid;
    ctx.beginPath();
    for (i = -R; i <= R; i++) {
      p0 = this.S(i, -R); p1 = this.S(i, R); ctx.moveTo(p0[0], p0[1]); ctx.lineTo(p1[0], p1[1]);
      p0 = this.S(-R, i); p1 = this.S(R, i); ctx.moveTo(p0[0], p0[1]); ctx.lineTo(p1[0], p1[1]);
    }
    ctx.stroke();
  };
  Scene.prototype.axes = function () {
    var ctx = this.ctx, R = this.gridN, a = this.S(-R, 0), b = this.S(R, 0), c = this.S(0, -R), d = this.S(0, R);
    ctx.lineWidth = 1.6; ctx.strokeStyle = this.pal.muted;
    ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.moveTo(c[0], c[1]); ctx.lineTo(d[0], d[1]); ctx.stroke();
  };
  // transformed grid: image of integer lattice under matrix M
  Scene.prototype.warpGrid = function (M, color, fill) {
    var ctx = this.ctx, R = this.gridN, k, A, B;
    if (fill) {
      ctx.fillStyle = fill;
      for (k = -R; k < R; k++) { /* subtle cell shading only along axes region, skip for perf */ }
    }
    ctx.lineWidth = 1.2; ctx.strokeStyle = color; ctx.globalAlpha = 1;
    ctx.beginPath();
    for (k = -R; k <= R; k++) {
      A = apply(M, k, -R); B = apply(M, k, R); var sa = this.S(A[0], A[1]), sb = this.S(B[0], B[1]);
      ctx.moveTo(sa[0], sa[1]); ctx.lineTo(sb[0], sb[1]);
      A = apply(M, -R, k); B = apply(M, R, k); sa = this.S(A[0], A[1]); sb = this.S(B[0], B[1]);
      ctx.moveTo(sa[0], sa[1]); ctx.lineTo(sb[0], sb[1]);
    }
    ctx.stroke();
  };
  Scene.prototype.arrow = function (x, y, color, width, label, opt) {
    opt = opt || {};
    var ctx = this.ctx, o = this.S(opt.ox || 0, opt.oy || 0), p = this.S(x, y);
    var dx = p[0] - o[0], dy = p[1] - o[1], len = Math.hypot(dx, dy);
    width = width || 3.2;
    ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = width; ctx.lineCap = 'round';
    if (len < 1) { ctx.beginPath(); ctx.arc(p[0], p[1], width, 0, TAU); ctx.fill(); }
    else {
      var ang = Math.atan2(dy, dx), hl = 10 + width * 1.4;
      var ex = p[0] - Math.cos(ang) * hl * 0.55, ey = p[1] - Math.sin(ang) * hl * 0.55;
      ctx.beginPath(); ctx.moveTo(o[0], o[1]); ctx.lineTo(ex, ey); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(p[0], p[1]);
      ctx.lineTo(p[0] - Math.cos(ang - 0.42) * hl, p[1] - Math.sin(ang - 0.42) * hl);
      ctx.lineTo(p[0] - Math.cos(ang + 0.42) * hl, p[1] - Math.sin(ang + 0.42) * hl);
      ctx.closePath(); ctx.fill();
    }
    if (label) {
      ctx.font = '700 13px ' + 'ui-monospace,Menlo,Consolas,monospace';
      ctx.fillStyle = color; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      var lx = p[0] + (opt.lx || 13 * Math.sign(dx || 1)), ly = p[1] + (opt.ly || -13);
      // halo
      ctx.save(); ctx.lineWidth = 3.5; ctx.strokeStyle = this.pal.surface; ctx.strokeText(label, lx, ly); ctx.restore();
      ctx.fillText(label, lx, ly);
    }
  };
  Scene.prototype.dot = function (x, y, color, r) {
    var ctx = this.ctx, p = this.S(x, y); ctx.fillStyle = color; ctx.beginPath(); ctx.arc(p[0], p[1], r || 5, 0, TAU); ctx.fill();
    ctx.lineWidth = 2; ctx.strokeStyle = this.pal.surface; ctx.stroke();
  };
  Scene.prototype.poly = function (pts, fill, stroke, w) {
    var ctx = this.ctx, i, s; ctx.beginPath();
    for (i = 0; i < pts.length; i++) { s = this.S(pts[i][0], pts[i][1]); if (i === 0) ctx.moveTo(s[0], s[1]); else ctx.lineTo(s[0], s[1]); }
    ctx.closePath();
    if (fill) { ctx.fillStyle = fill; ctx.fill(); }
    if (stroke) { ctx.lineWidth = w || 2; ctx.strokeStyle = stroke; ctx.stroke(); }
  };
  Scene.prototype.seg = function (x0, y0, x1, y1, color, w, dash) {
    var ctx = this.ctx, a = this.S(x0, y0), b = this.S(x1, y1);
    ctx.save(); if (dash) ctx.setLineDash(dash); ctx.lineWidth = w || 2; ctx.strokeStyle = color;
    ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke(); ctx.restore();
  };
  Scene.prototype.label = function (x, y, text, color, align) {
    var ctx = this.ctx, p = this.S(x, y);
    ctx.font = '700 13px ui-monospace,Menlo,Consolas,monospace';
    ctx.textAlign = align || 'left'; ctx.textBaseline = 'middle';
    ctx.lineWidth = 3.5; ctx.strokeStyle = this.pal.surface; ctx.strokeText(text, p[0], p[1]);
    ctx.fillStyle = color; ctx.fillText(text, p[0], p[1]);
  };
  // animation tween; cancels previous
  Scene.prototype.tween = function (ms, step, done) {
    var self = this, t0 = null; if (this._tw) cancelAnimationFrame(this._tw);
    function frame(ts) {
      if (t0 == null) t0 = ts; var t = clamp((ts - t0) / ms, 0, 1);
      step(easeInOut(t), t);
      if (t < 1) self._tw = requestAnimationFrame(frame); else { self._tw = 0; if (done) done(); }
    }
    this._tw = requestAnimationFrame(frame);
  };
  Scene.prototype.loop = function (step) {
    var self = this; this.stopLoop();
    function frame(ts) { step(ts); self._lp = requestAnimationFrame(frame); }
    this._lp = requestAnimationFrame(frame);
  };
  Scene.prototype.stopLoop = function () { if (this._lp) cancelAnimationFrame(this._lp); this._lp = 0; };

  // pointer dragging of world-space handles. handles: [{get:fn->[x,y], set:fn(x,y), r?}]
  Scene.prototype.draggable = function (handles, onChange) {
    var self = this, active = -1;
    function near(px, py) {
      for (var i = 0; i < handles.length; i++) {
        var w = handles[i].get(), s = self.S(w[0], w[1]);
        if (Math.hypot(px - s[0], py - s[1]) < (handles[i].r || 16)) return i;
      }
      return -1;
    }
    function pos(e) { var r = self.canvas.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; }
    this.canvas.addEventListener('pointerdown', function (e) {
      var p = pos(e); active = near(p[0], p[1]);
      if (active >= 0) { self.canvas.setPointerCapture(e.pointerId); self.canvas.classList.add('grabbing'); e.preventDefault(); }
    });
    this.canvas.addEventListener('pointermove', function (e) {
      var p = pos(e);
      if (active >= 0) {
        var w = self.W2(p[0], p[1]); handles[active].set(w[0], w[1]); if (onChange) onChange(); self.requestDraw(); e.preventDefault();
      } else { self.canvas.style.cursor = near(p[0], p[1]) >= 0 ? 'grab' : 'default'; }
    });
    function up(e) { if (active >= 0) { active = -1; self.canvas.classList.remove('grabbing'); } }
    this.canvas.addEventListener('pointerup', up);
    this.canvas.addEventListener('pointercancel', up);
  };

  /* ---------- DOM scaffolding helpers ---------- */
  function el(tag, cls, html) { var e = document.createElement(tag); if (cls) e.className = cls; if (html != null) e.innerHTML = html; return e; }
  function build(fig, cfg) {
    // cfg: {lab, title, sub, height, range, gridN, panx}
    fig.classList.add('viz');
    var lab = el('div', 'lab', cfg.lab || 'Interactive'); fig.appendChild(lab);
    if (cfg.title || cfg.sub) {
      var head = el('div', 'viz-head');
      if (cfg.title) head.appendChild(el('p', 'viz-title', cfg.title));
      if (cfg.sub) head.appendChild(el('p', 'viz-sub', cfg.sub));
      fig.appendChild(head);
    }
    var stage = el('div', 'viz-stage'); fig.appendChild(stage);
    var readout = el('div', 'viz-readout'); stage.appendChild(readout);
    var controls = el('div', 'viz-controls'); fig.appendChild(controls);
    var scene = new Scene(stage, { height: cfg.height, range: cfg.range, gridN: cfg.gridN, panx: cfg.panx, render: cfg.render });
    return { fig: fig, stage: stage, readout: readout, controls: controls, scene: scene };
  }
  function slider(controls, opts, onInput) {
    var wrap = el('div', 'viz-ctl');
    var lab = el('label'); var name = el('span', null, opts.name); var val = el('b', null, fmt(opts.value, opts.dp || 1));
    lab.appendChild(name); lab.appendChild(val);
    var inp = document.createElement('input'); inp.type = 'range';
    inp.min = opts.min; inp.max = opts.max; inp.step = opts.step || 0.1; inp.value = opts.value;
    inp.addEventListener('input', function () { val.textContent = fmt(parseFloat(inp.value), opts.dp || 1); onInput(parseFloat(inp.value)); });
    wrap.appendChild(lab); wrap.appendChild(inp); controls.appendChild(wrap);
    return { input: inp, setVal: function (v) { inp.value = v; val.textContent = fmt(v, opts.dp || 1); } };
  }
  function button(controls, label, cls, onClick) {
    var holder = controls.querySelector('.viz-btns') || (function () { var b = el('div', 'viz-btns'); controls.appendChild(b); return b; })();
    var b = el('button', 'viz-btn' + (cls ? ' ' + cls : ''), label); b.type = 'button';
    b.addEventListener('click', onClick); holder.appendChild(b); return b;
  }
  function caption(fig, html) { if (html) fig.appendChild(el('div', 'viz-cap', html)); }

  /* ============================================================
     WIDGETS
     ============================================================ */
  var WIDGETS = {};

  /* ---- 3.1  A 2-variable system = two lines; solution = intersection ---- */
  WIDGETS.linsys = function (fig, d) {
    // line 1: a1 x + b1 y = c1 ; line 2: a2 x + b2 y = c2  (drag a point on each line + its slope handle)
    var L1 = { a: 1, b: 1, c: 2 }, L2 = { a: 1, b: -1, c: 0 };
    var S = build(fig, { lab: 'Interactive · drag the dots', title: d.title || 'A system is lines meeting: one, none, or infinitely many', range: 5, render: draw });
    // represent each line by two draggable points on it
    var p1 = ptsOf(L1), p2 = ptsOf(L2);
    function ptsOf(L) {
      // pick two points on a x+b y=c
      if (Math.abs(L.b) > Math.abs(L.a)) { return [[-3, (L.c - L.a * -3) / L.b], [3, (L.c - L.a * 3) / L.b]]; }
      return [[(L.c - L.b * -3) / L.a, -3], [(L.c - L.b * 3) / L.a, 3]];
    }
    function lineFrom(P) { // through P[0],P[1]: returns {a,b,c} normalised
      var dx = P[1][0] - P[0][0], dy = P[1][1] - P[0][1];
      var a = dy, b = -dx, c = a * P[0][0] + b * P[0][1];
      return { a: a, b: b, c: c };
    }
    S.scene.draggable([
      { get: function () { return p1[0]; }, set: function (x, y) { p1[0] = [x, y]; } },
      { get: function () { return p1[1]; }, set: function (x, y) { p1[1] = [x, y]; } },
      { get: function () { return p2[0]; }, set: function (x, y) { p2[0] = [x, y]; } },
      { get: function () { return p2[1]; }, set: function (x, y) { p2[1] = [x, y]; } }
    ], upd);
    function solve() {
      var A = lineFrom(p1), B = lineFrom(p2), D = A.a * B.b - A.b * B.a;
      if (Math.abs(D) < 0.02) {
        // parallel: same line if constants proportional
        var same = Math.abs(A.a * B.c - B.a * A.c) < 0.08 && Math.abs(A.b * B.c - B.b * A.c) < 0.08;
        return { kind: same ? 'inf' : 'none' };
      }
      return { kind: 'one', x: (A.c * B.b - A.b * B.c) / D, y: (A.a * B.c - A.c * B.a) / D };
    }
    function upd() {
      var r = solve();
      S.readout.innerHTML = r.kind === 'one' ? 'lines cross once<br><b class="ok">unique</b>: (' + fmt(r.x, 1) + ', ' + fmt(r.y, 1) + ')'
        : r.kind === 'none' ? 'parallel, never meet<br><b class="bad">no solution</b>'
          : 'same line<br><b class="hot">infinitely many</b>';
    }
    function drawLine(s, P, col) {
      var A = lineFrom(P), R = s.gridN, pa, pb;
      if (Math.abs(A.b) > Math.abs(A.a)) { pa = [-R, (A.c - A.a * -R) / A.b]; pb = [R, (A.c - A.a * R) / A.b]; }
      else { pa = [(A.c - A.b * -R) / A.a, -R]; pb = [(A.c - A.b * R) / A.a, R]; }
      s.seg(pa[0], pa[1], pb[0], pb[1], col, 3.5);
    }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      drawLine(s, p1, s.pal.accent); drawLine(s, p2, s.pal.hot);
      s.dot(p1[0][0], p1[0][1], s.pal.accent); s.dot(p1[1][0], p1[1][1], s.pal.accent);
      s.dot(p2[0][0], p2[0][1], s.pal.hot); s.dot(p2[1][0], p2[1][1], s.pal.hot);
      var r = solve();
      if (r.kind === 'one') s.dot(r.x, r.y, s.pal.ok, 7);
      upd();
    }
    S.scene.requestDraw();
    caption(fig, 'Each equation in two unknowns draws a <b>line</b>. A solution is a point on <b>both</b>. Drag the endpoints: cross the lines for a <b>unique</b> solution, make them <b>parallel</b> for <b>none</b>, or lay them exactly on top of each other for <b>infinitely many</b>. Every linear system behaves this way.');
  };

  /* ---- 3.2  Vector as an arrow; coordinates are instructions ---- */
  WIDGETS.vector = function (fig, d) {
    var v = { x: +d.x || 3, y: +d.y || 2 };
    var S = build(fig, { lab: 'Interactive · drag the tip', title: d.title || 'A vector is an arrow — its coordinates are steps', range: 5, render: draw });
    S.scene.draggable([{ get: function () { return [v.x, v.y]; }, set: function (x, y) { v.x = Math.round(x * 2) / 2; v.y = Math.round(y * 2) / 2; } }], update);
    function update() { S.readout.innerHTML = 'v = (<b>' + fmt(v.x, 1) + '</b>, <b>' + fmt(v.y, 1) + '</b>)<br>length ‖v‖ = ' + fmt(Math.hypot(v.x, v.y), 2); }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      // step decomposition: along x then along y
      s.seg(0, 0, v.x, 0, s.pal.ihat, 3, [5, 5]);
      s.seg(v.x, 0, v.x, v.y, s.pal.jhat, 3, [5, 5]);
      s.arrow(v.x, v.y, s.pal.hot, 3.4, 'v');
      s.dot(v.x, v.y, s.pal.hot, 5);
    }
    update(); S.scene.requestDraw();
    caption(fig, 'Reading the coordinates <b>(x, y)</b> as instructions: walk <b>x</b> along the green axis, then <b>y</b> along the red one. Drag the tip.');
  };

  /* ---- 3.2  Linear combination a·v + b·w ---- */
  WIDGETS.lincomb = function (fig, d) {
    var v = { x: 2, y: 1 }, w = { x: -1, y: 1.5 }, a = 1, b = 1;
    var S = build(fig, { lab: 'Interactive', title: d.title || 'Linear combination: scale two vectors, then add', range: 6, render: draw });
    var sa = slider(S.controls, { name: 'a  (scales v)', min: -3, max: 3, step: 0.1, value: a, dp: 1 }, function (x) { a = x; S.scene.requestDraw(); upd(); });
    var sb = slider(S.controls, { name: 'b  (scales w)', min: -3, max: 3, step: 0.1, value: b, dp: 1 }, function (x) { b = x; S.scene.requestDraw(); upd(); });
    S.scene.draggable([
      { get: function () { return [v.x, v.y]; }, set: function (x, y) { v.x = x; v.y = y; } },
      { get: function () { return [w.x, w.y]; }, set: function (x, y) { w.x = x; w.y = y; } }
    ], upd);
    function upd() { S.readout.innerHTML = '<b class="hot">a</b>·v + <b class="ok">b</b>·w = (' + fmt(a * v.x + b * w.x, 1) + ', ' + fmt(a * v.y + b * w.y, 1) + ')'; }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var rx = a * v.x, ry = a * v.y;
      s.arrow(v.x, v.y, s.pal.ghost, 2.4, 'v');
      s.arrow(w.x, w.y, s.pal.ghost, 2.4, 'w');
      s.arrow(rx, ry, s.pal.hot, 3, 'a·v');                                   // scaled v
      s.seg(rx, ry, rx + b * w.x, ry + b * w.y, s.pal.ok, 3, [6, 5]);          // then add b·w (tip-to-tail)
      s.arrow(rx + b * w.x, ry + b * w.y, s.pal.accent, 3.6, 'a·v + b·w');
      s.dot(rx + b * w.x, ry + b * w.y, s.pal.accent, 5);
    }
    upd(); S.scene.requestDraw();
    caption(fig, 'Every reachable point is <b>a·v + b·w</b>: stretch v by a, stretch w by b, lay them tip-to-tail. Drag v and w, or move the sliders.');
  };

  /* ---- 3.2  Span of two vectors (line vs whole plane) ---- */
  WIDGETS.span = function (fig, d) {
    var v = { x: 2, y: 1 }, w = { x: -1, y: 2 };
    var S = build(fig, { lab: 'Interactive · drag v and w', title: d.title || 'Span = every point you can reach', range: 6, render: draw });
    S.scene.draggable([
      { get: function () { return [v.x, v.y]; }, set: function (x, y) { v.x = x; v.y = y; } },
      { get: function () { return [w.x, w.y]; }, set: function (x, y) { w.x = x; w.y = y; } }
    ], upd);
    function cross() { return v.x * w.y - v.y * w.x; }
    function upd() {
      var dep = Math.abs(cross()) < 0.08;
      S.readout.innerHTML = dep
        ? 'v and w are <b class="bad">parallel</b><br>span = a <b>line</b>'
        : 'v and w <b class="ok">independent</b><br>span = the <b>whole plane</b>';
    }
    function draw(s) {
      s.clear(); s.bgGrid();
      var dep = Math.abs(cross()) < 0.08, R = s.gridN;
      if (dep) {
        // span is a line through origin in direction of the (nonzero) vector
        var dir = (Math.hypot(v.x, v.y) > 0.1) ? v : w, n = Math.hypot(dir.x, dir.y) || 1;
        var ux = dir.x / n, uy = dir.y / n;
        s.seg(-ux * R, -uy * R, ux * R, uy * R, s.pal.hot, 10, null);
      } else {
        // whole plane reachable -> flood the visible area
        s.ctx.save(); s.ctx.globalAlpha = s.pal.dark ? 0.16 : 0.12; s.ctx.fillStyle = s.pal.accent;
        s.ctx.fillRect(0, 0, s.W, s.H); s.ctx.restore();
        // the lattice it generates
        s.warpGrid({ a: v.x, b: w.x, c: v.y, d: w.y }, s.pal.gridWarp);
      }
      s.axes();
      s.arrow(v.x, v.y, s.pal.hot, 3.4, 'v');
      s.arrow(w.x, w.y, s.pal.ok, 3.4, 'w');
      s.dot(v.x, v.y, s.pal.hot); s.dot(w.x, w.y, s.pal.ok);
    }
    upd(); S.scene.requestDraw();
    caption(fig, 'Two independent vectors reach <b>every</b> point (their combinations tile the plane). Make them <b>parallel</b> and the span collapses to a single line — the second vector became redundant.');
  };

  /* ---- 3.2  Independence: the parallelogram area ---- */
  WIDGETS.independence = function (fig, d) {
    var v = { x: 2.5, y: 0.5 }, w = { x: 1, y: 2 };
    var S = build(fig, { lab: 'Interactive', title: d.title || 'Independence ⇔ the parallelogram has area', range: 5, render: draw });
    S.scene.draggable([
      { get: function () { return [v.x, v.y]; }, set: function (x, y) { v.x = x; v.y = y; } },
      { get: function () { return [w.x, w.y]; }, set: function (x, y) { w.x = x; w.y = y; } }
    ], upd);
    function area() { return Math.abs(v.x * w.y - v.y * w.x); }
    function upd() {
      var A = area(), dep = A < 0.08;
      S.readout.innerHTML = 'area = <b>' + fmt(A, 2) + '</b><br>' + (dep ? '<b class="bad">dependent</b> (flat)' : '<b class="ok">independent</b>');
    }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var A = area(), dep = A < 0.08;
      s.poly([[0, 0], [v.x, v.y], [v.x + w.x, v.y + w.y], [w.x, w.y]], dep ? 'rgba(180,35,52,.16)' : (s.pal.dark ? 'rgba(95,207,147,.2)' : 'rgba(31,122,77,.16)'), dep ? s.pal.bad : s.pal.ok, 2);
      s.arrow(v.x, v.y, s.pal.hot, 3.2, 'v');
      s.arrow(w.x, w.y, s.pal.accent, 3.2, 'w');
      s.dot(v.x, v.y, s.pal.hot); s.dot(w.x, w.y, s.pal.accent);
    }
    upd(); S.scene.requestDraw();
    caption(fig, 'The two vectors span a parallelogram. Nonzero area ⇒ they point in genuinely different directions (<b>independent</b>). Line them up and the area drops to 0 ⇒ one is a multiple of the other (<b>dependent</b>).');
  };

  /* ---- 3.3  Matrix as a linear transformation of the whole plane ---- */
  WIDGETS.transform = function (fig, d) {
    var M = parseM(d.m, { a: 1, b: 1, c: 0, d: 1 });
    var cur = { a: M.a, b: M.b, c: M.c, d: M.d };     // live matrix (draggable basis)
    var tv = { x: 1, y: 1 };                          // a test vector (in original space)
    var S = build(fig, { lab: 'Interactive · drag î and ĵ', title: d.title || 'A matrix bends the grid: where do î and ĵ land?', range: 5, render: draw });
    var showV = true;
    S.scene.draggable([
      { get: function () { return [cur.a, cur.c]; }, set: function (x, y) { cur.a = snap(x); cur.c = snap(y); } },   // i-hat = col1
      { get: function () { return [cur.b, cur.d]; }, set: function (x, y) { cur.b = snap(x); cur.d = snap(y); } },   // j-hat = col2
      { get: function () { return [tv.x, tv.y]; }, set: function (x, y) { tv.x = snap(x); tv.y = snap(y); }, r: 14 }
    ], upd);
    button(S.controls, '▶ Animate from identity', '', function () { animTo(cur); });
    button(S.controls, 'Reset', 'ghost', function () { cur = { a: 1, b: 0, c: 0, d: 1 }; animTo(parseM(d.m, M)); });
    var tcur = null;   // non-null only while an animation is interpolating
    function animTo(target) { var from = { a: 1, b: 0, c: 0, d: 1 }; S.scene.tween(900, function (t) { tcur = lerpM(from, target, t); draw(S.scene); }, function () { tcur = null; S.scene.requestDraw(); }); }
    function upd() { var m = cur, img = apply(m, tv.x, tv.y); S.readout.innerHTML = 'M = [' + fmt(m.a, 1) + ' ' + fmt(m.b, 1) + '; ' + fmt(m.c, 1) + ' ' + fmt(m.d, 1) + ']<br>det = <b>' + fmt(det(m), 2) + '</b>' + (showV ? '<br>v=(' + fmt(tv.x, 1) + ',' + fmt(tv.y, 1) + ') → (' + fmt(img[0], 1) + ',' + fmt(img[1], 1) + ')' : ''); }
    function draw(s) {
      s.clear(); s.bgGrid();
      var m = tcur || cur;
      s.warpGrid(m, s.pal.gridWarp);
      s.axes();
      // i-hat, j-hat images
      s.arrow(m.a, m.c, s.pal.ihat, 3.6, 'î');
      s.arrow(m.b, m.d, s.pal.jhat, 3.6, 'ĵ');
      s.dot(m.a, m.c, s.pal.ihat); s.dot(m.b, m.d, s.pal.jhat);
      if (showV && !tcur) {
        var img = apply(m, tv.x, tv.y);
        s.arrow(tv.x, tv.y, s.pal.ghost, 2.4, 'v');
        s.arrow(img[0], img[1], s.pal.hot, 3.4, 'Mv');
        s.dot(tv.x, tv.y, s.pal.ghost); s.dot(img[0], img[1], s.pal.hot);
      }
      upd();
    }
    S.scene.requestDraw();
    caption(fig, 'The matrix is completely described by <b>where it sends î and ĵ</b> — the columns of M. Drag their tips and watch the entire grid follow, staying evenly spaced and parallel (that is what "linear" means). The orange arrow shows any vector riding along.');
    function snap(x) { return Math.round(x * 2) / 2; }
  };

  /* ---- 3.3  Composition: apply M then N ---- */
  WIDGETS.compose = function (fig, d) {
    var M = parseM(d.m, { a: 1, b: -0.5, c: 0, d: 1 });   // shear
    var N = parseM(d.n, { a: 0, b: -1, c: 1, d: 0 });     // rotate 90°
    var S = build(fig, { lab: 'Interactive', title: d.title || 'Composition NM: do one transformation, then the next', range: 5, render: draw });
    var shown = I2, stage = 0;
    button(S.controls, '▶ Apply M (shear)', '', function () { play([M], ['M']); });
    button(S.controls, '▶ then N (rotate)', '', function () { play([M, mul(N, M)], ['M', 'N∘M']); });
    button(S.controls, 'Reset', 'ghost', function () { shown = I2; stage = 0; S.readout.innerHTML = 'identity'; S.scene.requestDraw(); });
    function play(targets, names) {
      var from = I2, i = 0;
      function next() {
        if (i >= targets.length) return;
        var to = targets[i], nm = names[i], f = shown;
        S.scene.tween(750, function (t) { shown = lerpM(f, to, t); S.readout.innerHTML = 'after <b>' + nm + '</b>'; draw(S.scene); }, function () { shown = to; i++; setTimeout(next, 180); });
      }
      shown = I2; next();
    }
    function draw(s) { s.clear(); s.bgGrid(); s.warpGrid(shown, s.pal.gridWarp); s.axes(); s.arrow(shown.a, shown.c, s.pal.ihat, 3.4, 'î'); s.arrow(shown.b, shown.d, s.pal.jhat, 3.4, 'ĵ'); }
    S.readout.innerHTML = 'identity'; S.scene.requestDraw();
    caption(fig, 'Transformations stack: first shear the plane, then rotate it. The single matrix <b>N∘M</b> does both at once — this is exactly why matrix multiplication is defined the way it is, and why order matters (<b>NM ≠ MN</b>).');
  };

  /* ---- 3.3  Inverse undoes the transformation ---- */
  WIDGETS.inverse = function (fig, d) {
    var M = parseM(d.m, { a: 1.2, b: 0.8, c: -0.4, d: 1.1 });
    var S = build(fig, { lab: 'Interactive', title: d.title || 'The inverse rewinds the transformation', range: 5, render: draw });
    var shown = I2;
    button(S.controls, '▶ Apply M', '', function () { to(M, 'M'); });
    button(S.controls, '▶ Apply M⁻¹', '', function () { var mi = inv(M); if (mi) to(I2, 'M⁻¹M = I'); else S.readout.innerHTML = '<b class="bad">det = 0: no inverse</b>'; });
    button(S.controls, 'Reset', 'ghost', function () { shown = I2; S.readout.innerHTML = 'identity'; S.scene.requestDraw(); });
    function to(target, msg) { var f = shown; S.scene.tween(800, function (t) { shown = lerpM(f, target, t); draw(S.scene); }, function () { shown = target; S.readout.innerHTML = msg; }); }
    function draw(s) { s.clear(); s.bgGrid(); s.warpGrid(shown, s.pal.gridWarp); s.axes(); s.arrow(shown.a, shown.c, s.pal.ihat, 3.4, 'î'); s.arrow(shown.b, shown.d, s.pal.jhat, 3.4, 'ĵ'); }
    var D = det(M);
    S.readout.innerHTML = 'det M = <b>' + fmt(D, 2) + '</b>';
    S.scene.requestDraw();
    caption(fig, 'Apply <b>M</b> to warp the grid, then apply <b>M⁻¹</b> to snap it perfectly back to the start. The inverse exists precisely when <b>det M ≠ 0</b> — if M flattened the plane, no transformation could un-flatten it.');
  };

  /* ---- 3.3  Determinant as signed area ---- */
  WIDGETS.determinant = function (fig, d) {
    var cur = parseM(d.m, { a: 2, b: 0.5, c: 0.5, d: 1.5 });
    var S = build(fig, { lab: 'Interactive · drag î and ĵ', title: d.title || 'The determinant is the area scale factor', range: 4.5, render: draw });
    S.scene.draggable([
      { get: function () { return [cur.a, cur.c]; }, set: function (x, y) { cur.a = sn(x); cur.c = sn(y); } },
      { get: function () { return [cur.b, cur.d]; }, set: function (x, y) { cur.b = sn(x); cur.d = sn(y); } }
    ], upd);
    function upd() {
      var D = det(cur), flip = D < -1e-6, flat = Math.abs(D) < 0.05;
      S.readout.innerHTML = 'det = <b>' + fmt(D, 2) + '</b><br>' + (flat ? '<b class="bad">area → 0 (squashed)</b>' : flip ? '<b class="hot">flipped</b> (negative)' : 'area ×' + fmt(Math.abs(D), 2));
    }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var D = det(cur);
      // the unit square -> parallelogram
      s.poly([[0, 0], [1, 0], [1, 1], [0, 1]], 'rgba(120,120,120,.10)', s.pal.muted, 1.2);  // reference unit square
      var fill = D < -1e-6 ? (s.pal.dark ? 'rgba(255,176,77,.22)' : 'rgba(217,119,6,.18)') : (s.pal.dark ? 'rgba(123,162,232,.22)' : 'rgba(27,58,122,.16)');
      s.poly([[0, 0], [cur.a, cur.c], [cur.a + cur.b, cur.c + cur.d], [cur.b, cur.d]], fill, s.pal.accent, 2);
      s.arrow(cur.a, cur.c, s.pal.ihat, 3.4, 'î');
      s.arrow(cur.b, cur.d, s.pal.jhat, 3.4, 'ĵ');
      s.dot(cur.a, cur.c, s.pal.ihat); s.dot(cur.b, cur.d, s.pal.jhat);
      upd();
    }
    S.scene.requestDraw();
    caption(fig, 'The shaded parallelogram is the image of the unit square. Its area <b>is</b> |det M| — how much the transformation scales every area. Drag so î and ĵ line up: the area (and det) hits <b>0</b>. Cross them over and the det goes <b>negative</b> — space got flipped.');
    function sn(x) { return Math.round(x * 2) / 2; }
  };

  /* ---- 3.3  Rectangular map: 2D → 1D projection (dimension drop) ---- */
  WIDGETS.projection = function (fig, d) {
    var p = { x: 2, y: 1 };     // point in the plane
    var ang = 25 * Math.PI / 180; // direction of the output line
    var S = build(fig, { lab: 'Interactive · drag the point', title: d.title || 'A 2×1-shaped map sends the plane onto a line', range: 5, render: draw });
    var sa = slider(S.controls, { name: 'line angle°', min: 0, max: 180, step: 1, value: 25, dp: 0 }, function (x) { ang = x * Math.PI / 180; S.scene.requestDraw(); });
    S.scene.draggable([{ get: function () { return [p.x, p.y]; }, set: function (x, y) { p.x = x; p.y = y; } }], upd);
    function proj() { var ux = Math.cos(ang), uy = Math.sin(ang), t = p.x * ux + p.y * uy; return [ux * t, uy * t, t]; }
    function upd() { var q = proj(); S.readout.innerHTML = '(' + fmt(p.x, 1) + ', ' + fmt(p.y, 1) + ') ↦ <b>' + fmt(q[2], 2) + '</b><br>one number: a point on the line'; }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var R = s.gridN, ux = Math.cos(ang), uy = Math.sin(ang);
      s.seg(-ux * R, -uy * R, ux * R, uy * R, s.pal.accent, 6);    // the output line (the "1-D world")
      var q = proj();
      s.seg(p.x, p.y, q[0], q[1], s.pal.muted, 2, [5, 5]);          // drop perpendicular
      s.arrow(p.x, p.y, s.pal.hot, 3.2, 'v');
      s.dot(q[0], q[1], s.pal.accent, 6);
      upd();
    }
    S.scene.requestDraw();
    caption(fig, 'A non-square (here 1×2) matrix maps <b>between</b> dimensions. This one takes any 2-D vector and returns a single number — its shadow on the blue line. Information is lost: a whole perpendicular line of points collapses to the same output.');
  };

  /* ---- 3.3  Cramer's rule: unknowns as area ratios ---- */
  WIDGETS.cramer = function (fig, d) {
    // columns a1,a2 of coefficient matrix; b is the target
    var a1 = { x: 2, y: 1 }, a2 = { x: -1, y: 1.5 };
    var x = 1.2, y = 1;          // the (unknown) solution we let the user set
    var S = build(fig, { lab: 'Interactive · drag the solution dot', title: d.title || "Cramer's rule: each unknown is a ratio of areas", range: 6, render: draw });
    S.scene.draggable([
      { get: function () { return [x * a1.x + y * a2.x, x * a1.y + y * a2.y]; }, set: solveFromB, r: 15 },
      { get: function () { return [a1.x, a1.y]; }, set: function (nx, ny) { a1.x = nx; a1.y = ny; }, r: 13 },
      { get: function () { return [a2.x, a2.y]; }, set: function (nx, ny) { a2.x = nx; a2.y = ny; }, r: 13 }
    ], upd);
    function solveFromB(bx, by) { var D = a1.x * a2.y - a1.y * a2.x; if (Math.abs(D) < 0.05) return; x = (bx * a2.y - by * a2.x) / D; y = (a1.x * by - a1.y * bx) / D; }
    function upd() {
      var D = a1.x * a2.y - a1.y * a2.x, bx = x * a1.x + y * a2.x, by = x * a1.y + y * a2.y;
      var Dx = bx * a2.y - by * a2.x, Dy = a1.x * by - a1.y * bx;
      S.readout.innerHTML = 'x = Dx/D = ' + fmt(Dx, 1) + '/' + fmt(D, 1) + ' = <b class="hot">' + fmt(x, 2) + '</b><br>y = Dy/D = ' + fmt(Dy, 1) + '/' + fmt(D, 1) + ' = <b class="ok">' + fmt(y, 2) + '</b>';
    }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var bx = x * a1.x + y * a2.x, by = x * a1.y + y * a2.y;
      // area for x: parallelogram of (b, a2); area for y: (a1, b)
      s.poly([[0, 0], [bx, by], [bx + a2.x, by + a2.y], [a2.x, a2.y]], 'rgba(217,119,6,.16)', s.pal.hot, 1.5);   // Dx
      s.poly([[0, 0], [a1.x, a1.y], [a1.x + bx, a1.y + by], [bx, by]], 'rgba(31,122,77,.14)', s.pal.ok, 1.5);   // Dy
      s.arrow(a1.x, a1.y, s.pal.accent, 3, 'a₁');
      s.arrow(a2.x, a2.y, s.pal.accent, 3, 'a₂');
      s.arrow(bx, by, s.pal.ink, 3.4, 'b');
      s.dot(bx, by, s.pal.ink, 6);
      upd();
    }
    S.scene.requestDraw();
    caption(fig, "Solving <b>x·a₁ + y·a₂ = b</b>. Replace column 1 by <b>b</b> and its parallelogram area is <b>D<sub>x</sub></b>; replace column 2 and you get <b>D<sub>y</sub></b>. Each unknown is that area divided by the full area <b>D</b>. Drag <b>b</b> and watch the ratios track x and y.");
  };

  /* ---- 3.4  Dot product: projection, sign, angle ---- */
  WIDGETS.dot = function (fig, d) {
    var a = { x: 3, y: 1 }, b = { x: 1.5, y: 2.5 };
    var S = build(fig, { lab: 'Interactive · drag a and b', title: d.title || 'Dot product = projection × length', range: 5, render: draw });
    S.scene.draggable([
      { get: function () { return [a.x, a.y]; }, set: function (x, y) { a.x = x; a.y = y; } },
      { get: function () { return [b.x, b.y]; }, set: function (x, y) { b.x = x; b.y = y; } }
    ], upd);
    function dp() { return a.x * b.x + a.y * b.y; }
    function upd() {
      var v = dp(), na = Math.hypot(a.x, a.y), nb = Math.hypot(b.x, b.y), cos = v / (na * nb || 1), ang = Math.acos(clamp(cos, -1, 1)) * 180 / Math.PI;
      var cls = v > 0.05 ? 'ok' : v < -0.05 ? 'bad' : 'hot';
      S.readout.innerHTML = 'a·b = <b class="' + cls + '">' + fmt(v, 2) + '</b><br>angle = ' + fmt(ang, 0) + '°  ' + (Math.abs(v) < 0.05 ? '(⊥)' : v > 0 ? '(acute)' : '(obtuse)');
    }
    function draw(s) {
      s.clear(); s.bgGrid(); s.axes();
      var na2 = a.x * a.x + a.y * a.y, t = (a.x * b.x + a.y * b.y) / (na2 || 1), px = t * a.x, py = t * a.y;
      s.seg(b.x, b.y, px, py, s.pal.muted, 2, [5, 5]);              // projection line
      s.seg(0, 0, px, py, s.pal.hot, 6);                           // the projection on a
      s.arrow(a.x, a.y, s.pal.accent, 3.2, 'a');
      s.arrow(b.x, b.y, s.pal.ok, 3.2, 'b');
      s.dot(px, py, s.pal.hot, 5);
      upd();
    }
    S.scene.requestDraw();
    caption(fig, 'Drop <b>b</b> straight down onto the line of <b>a</b>: that shadow (orange), times ‖a‖, is <b>a·b</b>. Point them the same way ⇒ <b class="ok">positive</b>; make them perpendicular ⇒ the shadow vanishes and <b>a·b = 0</b>; open past 90° ⇒ <b class="bad">negative</b>.');
  };

  /* ---- 3.4  Cross product in 3-D ---- */
  WIDGETS.cross = function (fig, d) {
    var a = [2, 1, 0], b = [0.5, 2, 0], yaw = -0.6, pitch = 0.5;
    var S = build(fig, { lab: 'Interactive · drag to rotate · sliders set a, b', title: d.title || 'Cross product: a new vector ⟂ to both, length = area', range: 4, render: draw });
    var saz = slider(S.controls, { name: 'a_z', min: -3, max: 3, step: 0.5, value: 0, dp: 1 }, function (v) { a[2] = v; S.scene.requestDraw(); });
    var sbz = slider(S.controls, { name: 'b_z', min: -3, max: 3, step: 0.5, value: 0, dp: 1 }, function (v) { b[2] = v; S.scene.requestDraw(); });
    // drag to orbit
    (function () {
      var last = null;
      S.scene.canvas.addEventListener('pointerdown', function (e) { last = [e.clientX, e.clientY]; S.scene.canvas.setPointerCapture(e.pointerId); });
      S.scene.canvas.addEventListener('pointermove', function (e) { if (!last) return; yaw += (e.clientX - last[0]) * 0.01; pitch = clamp(pitch + (e.clientY - last[1]) * 0.01, -1.3, 1.3); last = [e.clientX, e.clientY]; S.scene.requestDraw(); });
      S.scene.canvas.addEventListener('pointerup', function () { last = null; });
    })();
    function cr(u, v) { return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; }
    function proj(P) { // 3D -> 2D isometric-ish
      var cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
      var X = P[0] * cy - P[1] * sy, Z = P[0] * sy + P[1] * cy, Y = P[2];
      var y2 = Y * cp - Z * sp;
      return [X, y2];
    }
    function arr3(s, P, color, w, label) {
      var o = proj([0, 0, 0]), p = proj(P), so = s.S(o[0], o[1]), sp = s.S(p[0], p[1]);
      var ctx = s.ctx; ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = w; ctx.lineCap = 'round';
      var ang = Math.atan2(sp[1] - so[1], sp[0] - so[0]), hl = 11;
      ctx.beginPath(); ctx.moveTo(so[0], so[1]); ctx.lineTo(sp[0] - Math.cos(ang) * hl * 0.5, sp[1] - Math.sin(ang) * hl * 0.5); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(sp[0], sp[1]); ctx.lineTo(sp[0] - Math.cos(ang - 0.4) * hl, sp[1] - Math.sin(ang - 0.4) * hl); ctx.lineTo(sp[0] - Math.cos(ang + 0.4) * hl, sp[1] - Math.sin(ang + 0.4) * hl); ctx.closePath(); ctx.fill();
      if (label) { ctx.font = '700 13px ui-monospace,monospace'; ctx.textAlign = 'center'; ctx.lineWidth = 3.5; ctx.strokeStyle = s.pal.surface; ctx.strokeText(label, sp[0] + 10, sp[1] - 8); ctx.fillStyle = color; ctx.fillText(label, sp[0] + 10, sp[1] - 8); }
    }
    function seg3(s, P, Q, color, w, dash) { var a2 = proj(P), b2 = proj(Q), sa = s.S(a2[0], a2[1]), sb = s.S(b2[0], b2[1]); var ctx = s.ctx; ctx.save(); if (dash) ctx.setLineDash(dash); ctx.strokeStyle = color; ctx.lineWidth = w; ctx.beginPath(); ctx.moveTo(sa[0], sa[1]); ctx.lineTo(sb[0], sb[1]); ctx.stroke(); ctx.restore(); }
    function poly3(s, pts, fill) { var ctx = s.ctx; ctx.beginPath(); for (var i = 0; i < pts.length; i++) { var q = proj(pts[i]), sp = s.S(q[0], q[1]); if (i === 0) ctx.moveTo(sp[0], sp[1]); else ctx.lineTo(sp[0], sp[1]); } ctx.closePath(); ctx.fillStyle = fill; ctx.fill(); }
    function draw(s) {
      s.clear();
      var R = 4;
      // faint axes
      seg3(s, [-R, 0, 0], [R, 0, 0], s.pal.grid, 1); seg3(s, [0, -R, 0], [0, R, 0], s.pal.grid, 1); seg3(s, [0, 0, -R], [0, 0, R], s.pal.grid, 1);
      s.label(proj([R, 0, 0])[0], proj([R, 0, 0])[1], 'x', s.pal.muted); s.label(proj([0, R, 0])[0], proj([0, R, 0])[1], 'y', s.pal.muted); s.label(proj([0, 0, R])[0], proj([0, 0, R])[1], 'z', s.pal.muted);
      var c = cr(a, b);
      poly3(s, [[0, 0, 0], a, [a[0] + b[0], a[1] + b[1], a[2] + b[2]], b], s.pal.dark ? 'rgba(123,162,232,.22)' : 'rgba(27,58,122,.15)'); // parallelogram
      arr3(s, a, s.pal.hot, 3.2, 'a'); arr3(s, b, s.pal.ok, 3.2, 'b'); arr3(s, c, s.pal.accent, 3.6, 'a×b');
      var area = Math.hypot(c[0], c[1], c[2]);
      S.readout.innerHTML = 'a×b = (' + fmt(c[0], 1) + ', ' + fmt(c[1], 1) + ', ' + fmt(c[2], 1) + ')<br>‖a×b‖ = <b>' + fmt(area, 2) + '</b> = area';
    }
    S.scene.requestDraw();
    caption(fig, 'The blue vector <b>a×b</b> stands perpendicular to the plane of <b>a</b> and <b>b</b> (right-hand rule), and its length equals the <b>area</b> of the shaded parallelogram. Drag to orbit the view; push a and b out of the plane with the z-sliders.');
  };

  /* ---- 3.5  Eigenvectors: the lines that don't turn ---- */
  WIDGETS.eigen = function (fig, d) {
    var cur = parseM(d.m, { a: 2, b: 1, c: 1, d: 2 });
    var S = build(fig, { lab: 'Interactive · drag î and ĵ', title: d.title || 'Eigenvectors: the directions a matrix only stretches', range: 5, render: draw });
    var ang = 0, spinning = true;
    S.scene.draggable([
      { get: function () { return [cur.a, cur.c]; }, set: function (x, y) { cur.a = sn(x); cur.c = sn(y); stop(); } },
      { get: function () { return [cur.b, cur.d]; }, set: function (x, y) { cur.b = sn(x); cur.d = sn(y); stop(); } }
    ]);
    function stop() { }
    button(S.controls, '⏯ Spin a test vector', '', function () { spinning = !spinning; });
    S.scene.loop(function () { if (spinning) { ang += 0.012; } S.scene.render(S.scene); });
    function draw(s) {
      s.clear(); s.bgGrid();
      s.warpGrid(cur, s.pal.gridWarp); s.axes();
      var e = eigen(cur);
      if (e.real) {
        eline(s, e.v1, s.pal.hot); if (!e.repeated) eline(s, e.v2, s.pal.info);
      }
      // a probe vector sweeping the circle; show input (ghost) and output
      var vx = Math.cos(ang) * 2.2, vy = Math.sin(ang) * 2.2, img = apply(cur, vx, vy);
      var onEig = e.real && (aligned([vx, vy], e.v1) || (!e.repeated && aligned([vx, vy], e.v2)));
      s.arrow(vx, vy, s.pal.ghost, 2.4, 'v');
      s.arrow(img[0], img[1], onEig ? s.pal.ok : s.pal.jhat, 3.4, 'Mv');
      s.dot(vx, vy, s.pal.ghost); s.dot(img[0], img[1], onEig ? s.pal.ok : s.pal.jhat);
      if (e.real) {
        S.readout.innerHTML = 'λ₁ = <b class="hot">' + fmt(e.l1, 2) + '</b>' + (e.repeated ? ' (repeated)' : '<br>λ₂ = <b class="info">' + fmt(e.l2, 2) + '</b>') + (onEig ? '<br><b class="ok">on an eigenline → stays put</b>' : '');
      } else { S.readout.innerHTML = '<b class="bad">no real eigenvalues</b><br>(a rotation — every direction turns)'; }
    }
    function aligned(u, w) { var c = u[0] * w[1] - u[1] * w[0], n = Math.hypot(u[0], u[1]) * Math.hypot(w[0], w[1]); return Math.abs(c) / (n || 1) < 0.06; }
    function eline(s, v, col) { var R = s.gridN; s.seg(-v[0] * R, -v[1] * R, v[0] * R, v[1] * R, col, 3.5, [9, 7]); }
    function sn(x) { return Math.round(x * 2) / 2; }
    caption(fig, 'As the grey vector sweeps the circle, its image (the coloured arrow) usually points somewhere <b>different</b>. But along the dashed <b>eigenlines</b> the output stays on the same line through the origin — it is only scaled, by the eigenvalue λ. Drag î and ĵ; if the matrix is a pure rotation, no real eigenlines exist.');
  };

  /* ---- 3.5  Diagonalisation: stretch along eigen-directions ---- */
  WIDGETS.diagonalize = function (fig, d) {
    var M = parseM(d.m, { a: 2, b: 1, c: 1, d: 2 });
    var e = eigen(M);
    var S = build(fig, { lab: 'Interactive', title: d.title || 'Diagonalisation: in the eigen-basis, A is pure scaling', range: 5, render: draw });
    var shown = I2;
    button(S.controls, '▶ Apply A', '', function () { if (!e.real) { S.readout.innerHTML = '<b class="bad">not diagonalisable over ℝ</b>'; return; } to(M); });
    button(S.controls, 'Reset', 'ghost', function () { shown = I2; S.readout.innerHTML = r0(); S.scene.requestDraw(); });
    function to(T) { var f = shown; S.scene.tween(1100, function (t) { shown = lerpM(f, T, t); draw(S.scene); }, function () { shown = T; }); }
    function r0() { return e.real ? 'λ₁=<b class="hot">' + fmt(e.l1, 2) + '</b>, λ₂=<b class="info">' + fmt(e.l2, 2) + '</b><br>scale each eigen-axis by its λ' : '<b class="bad">complex eigenvalues</b>'; }
    function draw(s) {
      s.clear(); s.bgGrid();
      // draw the eigen-grid (skew grid aligned to eigenvectors), transformed by "shown"
      if (e.real) {
        var P = { a: e.v1[0], b: e.v2[0], c: e.v1[1], d: e.v2[1] };     // eigenbasis
        // eigen-grid lines = image of integer combos of eigenvectors, then apply shown
        drawEigenGrid(s, P, shown);
        var l1 = apply(shown, e.v1[0], e.v1[1]), l2 = apply(shown, e.v2[0], e.v2[1]);
        var R = s.gridN;
        s.seg(-e.v1[0] * R, -e.v1[1] * R, e.v1[0] * R, e.v1[1] * R, s.pal.hot, 2.5, [8, 6]);
        s.seg(-e.v2[0] * R, -e.v2[1] * R, e.v2[0] * R, e.v2[1] * R, s.pal.info, 2.5, [8, 6]);
        s.arrow(l1[0], l1[1], s.pal.hot, 3.4, 'v₁');
        s.arrow(l2[0], l2[1], s.pal.info, 3.4, 'v₂');
      }
      s.warpGrid(shown, s.pal.gridWarp); s.axes();
    }
    function drawEigenGrid(s, P, T) {
      // lines parallel to each eigenvector, transformed by T
      var R = s.gridN, k, A, B;
      s.ctx.save(); s.ctx.globalAlpha = 0.5; s.ctx.lineWidth = 1; s.ctx.strokeStyle = s.pal.gridWarp;
      for (k = -R; k <= R; k++) {
        A = apply(T, P.a * k + P.b * -R, P.c * k + P.d * -R); B = apply(T, P.a * k + P.b * R, P.c * k + P.d * R);
        s.seg(A[0], A[1], B[0], B[1], s.pal.gridWarp, 1);
        A = apply(T, P.a * -R + P.b * k, P.c * -R + P.d * k); B = apply(T, P.a * R + P.b * k, P.c * R + P.d * k);
        s.seg(A[0], A[1], B[0], B[1], s.pal.gridWarp, 1);
      }
      s.ctx.restore();
    }
    S.readout.innerHTML = r0(); S.scene.requestDraw();
    caption(fig, 'The dashed lines are the two <b>eigen-directions</b>. Watch what <b>A</b> does: it simply <b>stretches along each dashed line</b> by that line’s eigenvalue λ — no rotation, no shear. That is the whole meaning of <b>A = PDP⁻¹</b>: pick the eigen-basis and the transformation becomes the diagonal matrix D of pure scalings.');
  };

  /* ---------- config parsing ---------- */
  function parseM(str, fb) {
    if (!str) return { a: fb.a, b: fb.b, c: fb.c, d: fb.d };
    var n = str.split(/[ ,;]+/).map(parseFloat).filter(function (x) { return !isNaN(x); });
    if (n.length >= 4) return { a: n[0], b: n[1], c: n[2], d: n[3] };
    return { a: fb.a, b: fb.b, c: fb.c, d: fb.d };
  }

  /* ---------- auto-mount ---------- */
  function mountAll() {
    var nodes = document.querySelectorAll('.viz[data-viz]');
    nodes.forEach(function (fig) {
      if (fig.getAttribute('data-mounted')) return;
      var name = fig.getAttribute('data-viz');
      if (!WIDGETS[name]) return;
      fig.setAttribute('data-mounted', '1');
      var data = {};
      for (var i = 0; i < fig.attributes.length; i++) { var at = fig.attributes[i]; if (at.name.indexOf('data-') === 0) data[at.name.slice(5)] = at.value; }
      try { WIDGETS[name](fig, data); } catch (e) { if (window.console) console.error('viz', name, e); }
    });
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', mountAll);
  else mountAll();
})();
