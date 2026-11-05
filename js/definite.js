/* definite.js — definite (and improper) integrals  ∫_a^b f dx.
 *
 * definite(tree, v, loSrc, hiSrc) returns
 *   { definite:true, steps:[Step], result (node|null), resultTex, approx, method, rules,
 *     divergent (0 | 1 | -1 | 'osc'), improper, antideriv, lo, hi, plot, consts }
 * or throws IntegrationError. Steps have the same shape as integrate.js's.
 *
 * Routes, first that works wins:
 *   1. odd symmetry on [-c, c]            → 0, even with no antiderivative
 *   2. Fundamental Theorem of Calculus    → F(b) − F(a), using Calc.integrate for F;
 *      the interval is split where f blows up or F jumps, ∞ bounds and singular ends become limits
 *   3. a table of famous definite integrals (Gaussian, Dirichlet, Gamma, …)
 *   4. numerical quadrature (tanh–sinh / exp–sinh), reported as ≈
 * Every exact answer is compared with the numerical value before it is shown. */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const { num, C, V, add, mul, pow, neg, fn, TEX, tex, key, evaluate } = Calc;

  const S = (n) => Calc.simplify(n);
  const P = (n) => Calc.present(n);
  const TX = (n) => Calc.texOf(n);
  const PI = Math.PI;
  const ONE = num(1), ZERO = num(0), HALF = num(1, 2), NEG1 = num(-1);
  const sqrtN = (n) => pow(n, HALF);
  const piN = () => C('pi');
  const stmt = (id) => (Calc.RULE_BY_ID && Calc.RULE_BY_ID[id] ? Calc.RULE_BY_ID[id].statement : '');
  const Err = () => Calc.IntegrationError || Error;
  const fail = (msg, extra) => Object.assign(new (Err())(msg), extra || {});

  /* ---------------- bounds ---------------- */
  class BoundError extends Error { constructor(message, pos) { super(message); this.pos = pos; this.bound = true; } }
  const INF_RE = /^([+-]?)\s*(inf|infinity|infty|oo|∞)$/i;
  function parseBound(src, v) {
    const s = String(src == null ? '' : src).trim();
    if (!s) throw new BoundError('Missing limit', 0);
    const m = INF_RE.exec(s);
    if (m) {
      const sg = m[1] === '-' ? -1 : 1;
      return { inf: sg, val: sg * Infinity, tex: sg < 0 ? '-\\infty' : '\\infty', src: (sg < 0 ? '-' : '') + 'inf' };
    }
    let node;
    try { node = S(Calc.parse(s)); } catch (e) { throw new BoundError(e.message, e.pos); }
    const fv = Calc.freeVars(node);
    if (v && fv.has(v)) throw new BoundError('A limit can\'t contain the variable of integration', 0);
    if (fv.size) throw new BoundError('Limits must be numbers (π, e, √2, ∞ are fine), not letters', 0);
    const val = evaluate(node, {});
    if (!isFinite(val)) throw new BoundError('This limit is not a real number', 0);
    return { inf: 0, node, val, tex: TX(node), src: s };
  }

  /* ---------------- tree helpers ---------------- */
  function substTree(n, name, t) {
    const g = (c) => substTree(c, name, t);
    switch (n.type) {
      case 'var': return n.name === name ? t : n;
      case 'add': return add(n.terms.map(g));
      case 'mul': return mul(n.factors.map(g));
      case 'pow': return pow(g(n.base), g(n.exp));
      case 'func': return n.base ? fn(n.name, g(n.arg), g(n.base)) : fn(n.name, g(n.arg));
      case 'neg': return neg(g(n.arg));
      case 'div': return Calc.div(g(n.num), g(n.den));
      default: return n;
    }
  }
  // print F with the variable replaced by the bound, e.g. 1^3/3 (the printer adds the brackets it needs)
  function texAt(F, v, bNode) {
    const B = P(bNode);
    const walk = (n) => {
      if (Array.isArray(n)) return n.map(walk);
      if (!n || typeof n !== 'object') return n;
      if (n.type === 'var') return n.name === v ? B : n;
      const out = {};
      for (const k in n) out[k] = walk(n[k]);
      return out;
    };
    return tex(walk(P(F)));
  }
  const wrapIf = (F, t) => (P(F).type === 'add' ? '\\left(' + t + '\\right)' : t);
  function body(f) {
    const p = P(f);
    const t = tex(p);
    return p.type === 'add' ? '\\left(' + t + '\\right)' : t;
  }
  const intAB = (f, v, a, b) => '\\int_{' + a.tex + '}^{' + b.tex + '} ' + body(f) + '\\,d' + tex(V(v));

  /* ---------------- numbers ---------------- */
  function ratApprox(q, maxD, tol) {
    if (!isFinite(q)) return null;
    for (let d = 1; d <= maxD; d++) {
      const p = Math.round(q * d);
      if (Math.abs(q - p / d) <= tol * Math.max(1, Math.abs(q))) return [p, d];
    }
    return null;
  }
  const BASES = [
    [1, () => ONE], [PI, piN], [Math.SQRT2, () => sqrtN(num(2))], [Math.sqrt(3), () => sqrtN(num(3))],
    [PI * PI, () => pow(piN(), num(2))], [Math.sqrt(PI), () => sqrtN(piN())], [Math.LN2, () => fn('ln', num(2))],
    [PI * Math.sqrt(3), () => mul([piN(), sqrtN(num(3))])], [PI * Math.SQRT2, () => mul([piN(), sqrtN(num(2))])],
    [Math.sqrt(5), () => sqrtN(num(5))], [Math.log(3), () => fn('ln', num(3))], [Math.E, () => C('e')],
    [PI * Math.LN2, () => mul([piN(), fn('ln', num(2))])], [Math.sqrt(2 * PI), () => sqrtN(mul([num(2), piN()]))],
    [Math.pow(PI, 4), () => pow(piN(), num(4))], [1 / Math.E, () => pow(C('e'), NEG1)],
  ];
  const ALG = BASES.slice(0, 4).filter((b, i) => i !== 1); // 1, √2, √3 (trig values)
  // a closed form for x: a small rational times one of the bases, or null
  function recognize(x, tol, maxD, bases) {
    tol = tol || 1e-10; maxD = maxD || 48; bases = bases || BASES;
    if (!isFinite(x)) return null;
    if (Math.abs(x) < tol) return ZERO;
    for (let d = 1; d <= maxD; d++) {
      for (const [bv, mk] of bases) {
        const q = (x / bv) * d, p = Math.round(q);
        if (p !== 0 && Math.abs(q - p) <= tol * d * Math.max(1, Math.abs(x / bv))) return S(mul([num(p, d), mk()]));
      }
    }
    return null;
  }
  const floatNode = (x) => ({ type: 'num', n: x, d: 1, f: true });
  function fmtNum(x, sig) {
    if (!isFinite(x)) return x > 0 ? '\\infty' : x < 0 ? '-\\infty' : '\\text{undefined}';
    if (x === 0) return '0';
    const s = Number(x.toPrecision(sig || 10));
    const a = Math.abs(s);
    if (a >= 1e-4 && a < 1e10) return String(s);
    const [m, e] = s.toExponential(Math.max(0, (sig || 10) - 1)).split('e');
    return String(Number(m)) + ' \\times 10^{' + parseInt(e, 10) + '}';
  }
  // nice value for a point found numerically: rational or rational·π
  function snap(x) {
    const r = ratApprox(x, 12, 1e-9);
    if (r) { const n = num(r[0], r[1]); return { node: n, val: r[0] / r[1], tex: TX(n) }; }
    const q = ratApprox(x / PI, 12, 1e-9);
    if (q) { const n = S(mul([num(q[0], q[1]), piN()])); return { node: n, val: (q[0] / q[1]) * PI, tex: TX(n) }; }
    const n = floatNode(x);
    return { node: n, val: x, tex: fmtNum(x, 8) };
  }

  /* ---------------- exact values of trig functions at nice angles ---------------- */
  const TRIG = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc']);
  const INVT = new Set(['asin', 'acos', 'atan', 'acot', 'asec', 'acsc']);
  function exactify(n) {
    if (!n || typeof n !== 'object') return n;
    let m;
    switch (n.type) {
      case 'add': m = S(add(n.terms.map(exactify))); break;
      case 'mul': m = S(mul(n.factors.map(exactify))); break;
      case 'pow': m = S(pow(exactify(n.base), exactify(n.exp))); break;
      case 'func': m = S(n.base ? fn(n.name, exactify(n.arg), exactify(n.base)) : fn(n.name, exactify(n.arg))); break;
      default: return n;
    }
    if (m.type === 'func' && Calc.freeVars(m).size === 0) {
      const val = evaluate(m, {});
      if (TRIG.has(m.name) && ratApprox(evaluate(m.arg, {}) / PI, 12, 1e-12) && isFinite(val) && Math.abs(val) < 1e9) {
        const r = recognize(val, 1e-11, 6, ALG);
        if (r) return r;
      }
      if (INVT.has(m.name) && isFinite(val)) {
        const q = ratApprox(val / PI, 12, 1e-12);
        if (q) return S(mul([num(q[0], q[1]), piN()]));
      }
    }
    return m;
  }

  /* ---------------- numerical quadrature (double-exponential) ---------------- */
  // ∫_a^b g, a < b finite. Handles integrable endpoint singularities.
  function tanhSinh(g, a, b) {
    const c = (a + b) / 2, d = (b - a) / 2;
    let prev = null, I = 0, tail = 0, bad = false, err = Infinity;
    for (let lev = 0, h = 0.5; lev <= 7; lev++, h /= 2) {
      let sum = (PI / 2) * g(c);
      if (!isFinite(sum)) { bad = true; sum = 0; }
      tail = 0;
      for (let k = 1; k * h <= 4.2; k++) {
        const t = k * h, u = (PI / 2) * Math.sinh(t), ch = Math.cosh(u);
        const w = ((PI / 2) * Math.cosh(t)) / (ch * ch);
        const dist = (d * 2) / (1 + Math.exp(2 * u));
        if (dist === 0 || w === 0) break;
        const fl = g(a + dist), fr = g(b - dist);
        let term = w * ((isFinite(fl) ? fl : 0) + (isFinite(fr) ? fr : 0));
        if (!isFinite(fl) || !isFinite(fr)) { if (t < 3) bad = true; term = 0; }
        sum += term;
        tail = Math.abs(term);
      }
      I = d * h * sum;
      tail *= d;
      if (prev !== null) err = Math.abs(I - prev);
      if (lev >= 3 && err <= 1e-10 * Math.max(1, Math.abs(I))) break;
      prev = I;
    }
    return { val: I, err, ok: !bad && isFinite(I) && err <= 1e-7 * Math.max(1, Math.abs(I)) && tail <= 1e-8 * Math.max(1, Math.abs(I)) };
  }
  // ∫_0^∞ g
  function expSinh(g) {
    let prev = null, I = 0, tail = 0, bad = false, err = Infinity;
    for (let lev = 0, h = 0.5; lev <= 7; lev++, h /= 2) {
      let sum = 0;
      tail = 0;
      for (let k = -Math.floor(4 / h); k * h <= 4; k++) {
        const t = k * h, x = Math.exp((PI / 2) * Math.sinh(t));
        const w = (PI / 2) * Math.cosh(t) * x;
        const y = g(x);
        let term = w * y;
        if (!isFinite(term)) { if (Math.abs(t) < 3) bad = true; term = 0; }
        sum += term;
        if (Math.abs(t) > 3.5) tail = Math.max(tail, Math.abs(term));
      }
      I = h * sum;
      if (prev !== null) err = Math.abs(I - prev);
      if (lev >= 3 && err <= 1e-10 * Math.max(1, Math.abs(I))) break;
      prev = I;
    }
    return { val: I, err, ok: !bad && isFinite(I) && err <= 1e-7 * Math.max(1, Math.abs(I)) && tail <= 1e-9 * Math.max(1, Math.abs(I)) };
  }
  function quad(g, a, b) {
    if (a === -Infinity && b === Infinity) {
      const r1 = expSinh((x) => g(-x)), r2 = expSinh(g);
      return { val: r1.val + r2.val, err: r1.err + r2.err, ok: r1.ok && r2.ok };
    }
    if (b === Infinity) return expSinh((x) => g(a + x));
    if (a === -Infinity) return expSinh((x) => g(b - x));
    return tanhSinh(g, a, b);
  }
  function quadPieces(g, pts) {
    let val = 0, err = 0, ok = true;
    for (let i = 0; i + 1 < pts.length; i++) {
      const r = quad(g, pts[i].val, pts[i + 1].val);
      val += r.val; err += r.err; ok = ok && r.ok;
    }
    return { val, err, ok };
  }

  /* ---------------- looking at f on the interval ---------------- */
  const VALS = { a: 1.37, b: 0.73, c: 2.11, k: 1.61, m: 1.29, n: 2.3, p: 0.83, q: 1.17, r: 1.43, s: 0.91 };
  function constEnv(consts, alt) {
    const env = {};
    consts.forEach((c) => { env[c] = (VALS[c] || 1.19) * (alt ? 1.731 : 1); });
    return env;
  }
  function makeF(expr, env, v) {
    const e = Object.assign({}, env);
    return (x) => { e[v] = x; return evaluate(expr, e); };
  }
  function windowOf(a, b) {
    if (isFinite(a) && isFinite(b)) return [a, b];
    if (!isFinite(a) && !isFinite(b)) return [-40, 40];
    if (isFinite(a)) return [a, a + Math.max(40, 4 * Math.abs(a))];
    return [b - Math.max(40, 4 * Math.abs(b)), b];
  }
  // does |f| blow up as x → c from side s (+1 right, −1 left)?
  function blowsUp(f, c, s) {
    const sc = Math.max(1, Math.abs(c));
    const y1 = Math.abs(f(c + s * 1e-3 * sc)), y2 = Math.abs(f(c + s * 1e-9 * sc));
    if (!isFinite(y2)) return isFinite(y1) || Math.abs(f(c + s * 1e-2 * sc)) < Infinity;
    return y2 > 1e3 && y2 > 100 * y1;
  }
  function scan(f, lo, hi) {
    const N = 1600, h = (hi - lo) / N;
    const xs = [], ys = [];
    for (let i = 0; i <= N; i++) { const x = lo + i * h; xs.push(x); ys.push(f(x)); }
    const fin = ys.filter((y) => isFinite(y)).map(Math.abs).sort((p, q) => p - q);
    const scale = (fin.length ? fin[fin.length >> 1] : 0) + 1e-9;
    let gap = false;
    const cands = [];
    for (let i = 1; i < N; i++) {
      const y = ys[i];
      if (!isFinite(y)) {
        if (Number.isNaN(y) && (Number.isNaN(ys[i - 1]) || Number.isNaN(ys[i + 1]))) gap = true;
        cands.push(xs[i]);
        continue;
      }
      const yl = Math.abs(ys[i - 1]), yr = Math.abs(ys[i + 1]);
      if (Math.abs(y) > 1e3 * scale && Math.abs(y) >= yl && Math.abs(y) >= yr) cands.push(peak(f, xs[i - 1], xs[i + 1]));
    }
    for (let i = 0; i < N; i++) {
      const y0 = ys[i], y1 = ys[i + 1];
      if (isFinite(y0) && isFinite(y1) && y0 * y1 < 0 && Math.min(Math.abs(y0), Math.abs(y1)) > 50 * scale) cands.push(bisectSign(f, xs[i], xs[i + 1]));
    }
    const sing = [];
    for (const x of cands) {
      if (!(blowsUp(f, x, 1) || blowsUp(f, x, -1))) continue;
      const p = snap(x);
      if (!sing.some((q) => Math.abs(q.val - p.val) < 1e-6 * Math.max(1, Math.abs(p.val)))) sing.push(Object.assign(p, { inf: 0, kind: 'sing' }));
    }
    sing.sort((p, q) => p.val - q.val);
    return { sing, gap };
  }
  function bisectSign(f, l, r) {
    let fl = f(l);
    for (let i = 0; i < 90 && r - l > 1e-15 * Math.max(1, Math.abs(l)); i++) {
      const m = (l + r) / 2, fm = f(m);
      if (!isFinite(fm)) return m;
      if (fm * fl < 0) r = m; else { l = m; fl = fm; }
    }
    return (l + r) / 2;
  }
  function peak(f, l, r) {
    for (let i = 0; i < 100 && r - l > 1e-15 * Math.max(1, Math.abs(l)); i++) {
      const m1 = l + (r - l) / 3, m2 = r - (r - l) / 3;
      const a1 = Math.abs(f(m1)), a2 = Math.abs(f(m2));
      if (!isFinite(a1)) return m1;
      if (!isFinite(a2)) return m2;
      if (a1 < a2) l = m1; else r = m2;
    }
    return (l + r) / 2;
  }
  function endInfo(f, c, s) {
    const y = f(c);
    return { undef: !isFinite(y), blow: blowsUp(f, c, s) };
  }
  // f(−x) = σ f(x) at sample points (σ = −1 odd, +1 even)
  function parity(f, c, sigma) {
    const pts = isFinite(c) ? [0.13, 0.29, 0.41, 0.57, 0.73, 0.88, 0.97].map((t) => t * c) : [0.3, 0.7, 1.3, 2.1, 3.7, 5.2, 8.8];
    let good = 0;
    for (const x of pts) {
      const p = f(x), m = f(-x);
      if (!isFinite(p) || !isFinite(m)) continue;
      if (Math.abs(m - sigma * p) > 1e-9 * (1 + Math.abs(p))) return false;
      good++;
    }
    return good >= 4;
  }

  /* ---------------- limits of F ---------------- */
  // numerical limit of F at c (±∞, or finite from side s)
  function limitNum(Fx, c, s) {
    const xs = [];
    if (!isFinite(c)) for (let k = 1; k <= 12; k++) xs.push(Math.sign(c) * Math.pow(10, k));
    else for (let k = 2; k <= 12; k++) xs.push(c + s * Math.pow(10, -k) * Math.max(1, Math.abs(c)));
    const ys = xs.map(Fx);
    const fin = ys.filter((y) => isFinite(y));
    const lastRaw = ys[ys.length - 1];
    if (lastRaw === Infinity || lastRaw === -Infinity) return { div: Math.sign(lastRaw) };
    if (fin.length < 5) return { none: true };
    const y = fin.slice(-6);
    const n = y.length, last = y[n - 1];
    const diffs = [];
    for (let i = 1; i < n; i++) diffs.push(y[i] - y[i - 1]);
    const ad = diffs.map(Math.abs);
    if (ad[ad.length - 1] <= 1e-6 * (1 + Math.abs(last)) && ad[ad.length - 2] <= 1e-4 * (1 + Math.abs(last))) {
      return { val: last, err: ad[ad.length - 1] };
    }
    // power-law convergence (e.g. 2√t → 0): the steps shrink geometrically, so sum the remaining tail
    const sameSign = diffs.every((d) => d > 0) || diffs.every((d) => d < 0);
    const ratios = [];
    for (let i = 1; i < ad.length; i++) ratios.push(ad[i] / ad[i - 1]);
    if (sameSign && ratios.every((r) => r < 0.8) && Math.abs(ratios[ratios.length - 1] - ratios[ratios.length - 2]) < 0.05) {
      const r = ratios[ratios.length - 1], tail = (diffs[diffs.length - 1] * r) / (1 - r);
      if (Math.abs(tail) < 1e-3 * (1 + Math.abs(last))) return { val: last + tail, err: Math.abs(tail) * 0.01 + 1e-12 };
    }
    const mono = diffs.every((d) => d > 0) || diffs.every((d) => d < 0);
    if (mono && (Math.abs(last) > 1e6 || ad[ad.length - 1] > 0.3 * ad[0])) return { div: Math.sign(diffs[diffs.length - 1]) };
    return { none: true };
  }

  /* ---------------- FTC ---------------- */
  const simpson = (f, l, r) => ((r - l) / 6) * (f(l) + 4 * f((l + r) / 2) + f(r));
  // points inside (p, q) where the antiderivative F jumps although f is fine; null = F unusable
  function findJumps(Fx, fx, p, q) {
    const [lo, hi] = windowOf(p.val, q.val);
    const N = 1200, h = (hi - lo) / N;
    const skip = 3;
    const F = [], f = [];
    for (let i = 0; i <= N; i++) { F.push(Fx(lo + i * h)); f.push(fx(lo + i * h)); }
    const bad = [];
    let nonFinite = 0;
    for (let i = skip; i < N - skip; i++) {
      if (!isFinite(f[i]) || !isFinite(f[i + 1])) continue;
      if (!isFinite(F[i]) || !isFinite(F[i + 1])) { nonFinite++; bad.push(i); continue; }
      const dF = F[i + 1] - F[i], tr = (h * (f[i] + f[i + 1])) / 2;
      if (Math.abs(dF - tr) > 1e-3 * (1 + Math.abs(dF) + Math.abs(tr))) bad.push(i);
    }
    if (nonFinite > 20) return null;
    const out = [];
    for (const i of bad) {
      let l = lo + i * h, r = l + h;
      const mis = (a, b) => { const d = Fx(b) - Fx(a); return isFinite(d) ? Math.abs(d - simpson(fx, a, b)) : Infinity; };
      for (let k = 0; k < 60 && r - l > 1e-14 * Math.max(1, Math.abs(l)); k++) {
        const m = (l + r) / 2;
        if (mis(l, m) >= mis(m, r)) r = m; else l = m;
      }
      const x = (l + r) / 2;
      const dlt = 1e-9 * Math.max(1, Math.abs(x));
      const jl = Fx(x - dlt), jr = Fx(x + dlt);
      if (isFinite(jl) && isFinite(jr) && Math.abs(jr - jl) < 1e-5 * (1 + Math.abs(jl))) continue;
      const sp = snap(x);
      if (sp.val <= p.val || sp.val >= q.val) continue;
      if (!out.some((o) => Math.abs(o.val - sp.val) < 1e-6 * Math.max(1, Math.abs(sp.val)))) out.push(Object.assign(sp, { inf: 0, kind: 'jump' }));
      if (out.length > 12) return null;
    }
    return out;
  }

  function limitNode(ctx, F, c, s) {
    const L = limitNum(makeF(F, ctx.env, ctx.v), c, s);
    if (L.div || L.none) return L;
    const tol = Math.min(1e-6, Math.max(1e-10, (50 * L.err) / Math.max(1, Math.abs(L.val))));
    let node = recognize(L.val, tol);
    if (node && ctx.consts.length) {
      // the same closed form must come out with other values of the constants
      const L2 = limitNum(makeF(F, ctx.env2, ctx.v), c, s);
      const n2 = L2.val !== undefined ? recognize(L2.val, tol) : null;
      if (!n2 || key(n2) !== key(node)) node = null;
    }
    return { val: L.val, node };
  }

  // value of F at an end of a piece, from inside the piece (s = +1: lower end, approached from the right)
  function endValue(ctx, F, Fx, pt, s) {
    const vt = tex(V(ctx.v));
    const Fdisp = wrapIf(F, TX(F));
    const limTex = (c) => '\\lim_{' + vt + '\\to ' + c + '} ' + Fdisp;
    if (pt.inf) {
      const L = limitNode(ctx, F, pt.val, s);
      return Object.assign(L, { disp: limTex(pt.tex), limit: true });
    }
    const c = pt.val, Fc = Fx(c);
    const near = Fx(c + s * 1e-12 * Math.max(1, Math.abs(c)));
    const sideTex = '{' + (pt.tex.length > 12 ? '(' + pt.tex + ')' : pt.tex) + '}^{' + (s > 0 ? '+' : '-') + '}';
    if (pt.kind !== 'jump' && isFinite(Fc) && isFinite(near) && Math.abs(near - Fc) < 1e-4 * (1 + Math.abs(Fc))) {
      let node = exactify(S(substTree(F, ctx.v, pt.node)));
      const nv = evaluate(node, ctx.env);
      if (!(Math.abs(nv - Fc) <= 1e-8 * (1 + Math.abs(Fc)))) node = ctx.consts.length ? null : recognize(Fc) || floatNode(Fc);
      const improperEnd = !!(pt.improper);
      return { node, val: Fc, disp: improperEnd ? limTex(sideTex) : wrapIf(F, texAt(F, ctx.v, pt.node)), limit: improperEnd };
    }
    const L = limitNode(ctx, F, c, s);
    return Object.assign(L, { disp: limTex(sideTex), limit: true });
  }
  const valTex = (e) => (e.div ? (e.div > 0 ? '\\infty' : '-\\infty') : e.none ? '\\text{(no limit)}' : e.node ? TX(e.node) : fmtNum(e.val));
  const minusTex = (t) => (/^-|[+-]/.test(t.replace(/^\\left\(.*\\right\)$/, '')) ? '\\left(' + t + '\\right)' : t);

  function tryFTC(ctx, a, b, sing) {
    let res;
    try { res = Calc.integrate(ctx.f, ctx.v); } catch (e) { ctx.nonElem = !!e.nonElementary; return null; } finally { Calc.setVar(ctx.v); }
    if (res.posOnly && a.val < 0) return null;
    const F = res.result;
    const Fx = makeF(F, ctx.env, ctx.v);
    const base = [a].concat(sing, [b]);
    let jumps = [];
    for (let i = 0; i + 1 < base.length; i++) {
      const j = findJumps(Fx, ctx.fx, base[i], base[i + 1]);
      if (j === null) return null;
      jumps = jumps.concat(j);
    }
    const pts = [a].concat(sing.concat(jumps).sort((p, q) => p.val - q.val), [b]);
    const pieces = [];
    for (let i = 0; i + 1 < pts.length; i++) {
      const p = pts[i], q = pts[i + 1];
      pieces.push({ p, q, lo: endValue(ctx, F, Fx, p, 1), hi: endValue(ctx, F, Fx, q, -1) });
    }
    // divergence: ∞ − ∞ or a missing limit means the integral diverges
    let divSign = 0, osc = false;
    for (const pc of pieces) {
      if (pc.hi.none || pc.lo.none) osc = true;
      const ds = [pc.hi.div || 0, -(pc.lo.div || 0)].filter(Boolean);
      for (const d of ds) { if (divSign && d !== divSign) osc = true; divSign = d; }
    }
    const vt = tex(V(ctx.v));
    const antiStep = Object.assign({}, res.steps[0], { caption: 'Find an antiderivative' });
    const improper = pieces.some((pc) => pc.lo.limit || pc.hi.limit);
    const pieceRules = improper ? ['ftc', 'improperDef'] : ['ftc'];
    const evalTex = (pc) => pc.hi.disp + ' - ' + minusTex(pc.lo.disp);
    const combTex = (pc) => valTex(pc.hi) + ' - ' + minusTex(valTex(pc.lo));
    const pieceVal = (pc) => (pc.hi.div || pc.lo.div || pc.hi.none || pc.lo.none ? null : pc.hi.node && pc.lo.node ? S(add([pc.hi.node, neg(pc.lo.node)])) : undefined);
    const divergent = osc ? 'osc' : divSign;
    let value = null, approx = null;
    if (!divergent) {
      approx = pieces.reduce((s, pc) => s + pc.hi.val - pc.lo.val, 0);
      const vals = pieces.map(pieceVal);
      if (vals.every((x) => x)) {
        value = exactify(S(add(vals)));
        const nv = evaluate(value, ctx.env);
        if (!(Math.abs(nv - approx) <= 1e-7 * Math.max(1, Math.abs(approx)))) value = ctx.consts.length ? null : recognize(approx);
      } else if (!ctx.consts.length) value = recognize(approx, 1e-9);
    }
    if (!divergent && value === null && ctx.consts.length) return null;
    const resTex = divergent ? divTex(divergent) : value ? TX(value) : '\\approx ' + fmtNum(approx);
    const Ftex = TX(F);
    let step;
    if (pieces.length === 1) {
      const pc = pieces[0];
      step = {
        lhsTex: intAB(ctx.f, ctx.v, a, b), rules: pieceRules, children: [antiStep],
        formula: improper ? stmt('improperDef') : stmt('ftc'), where: 'F(' + vt + ') = ' + Ftex,
        back: improper ? evalTex(pc) : '\\Big[' + Ftex + '\\Big]_{' + a.tex + '}^{' + b.tex + '} = ' + evalTex(pc), backLabel: 'Evaluate',
        combinedTex: combTex(pc), resultTex: resTex,
      };
    } else {
      const why = pts.slice(1, -1).map((p) => p.tex + (p.kind === 'jump' ? '\\ (F\\text{ jumps})' : '\\ (f\\text{ blows up})')).join(',\\ ');
      const kids = pieces.map((pc) => {
        const pv = pieceVal(pc);
        const pr = pv ? TX(exactify(pv)) : valTex(pc.hi.div || pc.hi.none ? pc.hi : pc.lo.div || pc.lo.none ? Object.assign({}, pc.lo, { div: -(pc.lo.div || 0) || pc.lo.div }) : { val: pc.hi.val - pc.lo.val });
        return {
          lhsTex: intAB(ctx.f, ctx.v, pc.p, pc.q), rules: pc.hi.limit || pc.lo.limit ? ['ftc', 'improperDef'] : ['ftc'], children: [],
          setup: evalTex(pc), combinedTex: combTex(pc), resultTex: pr,
        };
      });
      step = {
        lhsTex: intAB(ctx.f, ctx.v, a, b), rules: ['intProps'], children: [antiStep].concat(kids),
        formula: stmt('intProps'), where: 'F(' + vt + ') = ' + Ftex,
        note: { label: 'Split at', tex: why },
        combinedTex: divergent ? null : kids.map((k) => k.resultTex).join(' + ').replace(/\+ -/g, '- '), resultTex: resTex,
      };
    }
    return {
      step, value, approx: value ? evaluate(value, ctx.env) : approx, divergent, method: 'ftc', improper,
      antideriv: { result: F, resultTex: res.resultTex, check: res.check }, pts,
    };
  }
  const divTex = (d) => (d === 1 ? '\\infty' : d === -1 ? '-\\infty' : '\\text{diverges}');

  /* ---------------- famous definite integrals ---------------- */
  const KS = [1, 2, 3, 4, 5, 6, 8, 10, 1 / 2, 1 / 3, 1 / 4, 3 / 2, 2 / 3, 5 / 2, 1 / 5, 1 / 10];
  const kNode = (k) => { const r = ratApprox(k, 10, 1e-12); return num(r[0], r[1]); };
  const fact = (n) => (n <= 1 ? 1 : n * fact(n - 1));
  const kWhere = (sym) => (p) => sym + ' = ' + TX(kNode(p.k));
  const TABLE = [
    { rule: 'gaussianInt', even: true, params: KS.map((k) => ({ k })), g: (x, p) => Math.exp(-p.k * x * x),
      value: (p) => S(mul([HALF, sqrtN(mul([piN(), pow(kNode(p.k), NEG1)]))])), where: kWhere('a') },
    { rule: 'dirichletInt', even: true, params: KS.map((k) => ({ k })), g: (x, p) => Math.sin(p.k * x) / x,
      value: () => S(mul([HALF, piN()])), where: kWhere('k') },
    { rule: 'sinc2Int', even: true, params: KS.map((k) => ({ k })), g: (x, p) => Math.pow(Math.sin(p.k * x) / x, 2),
      value: (p) => S(mul([HALF, kNode(p.k), piN()])), where: kWhere('k') },
    { rule: 'gammaInt', even: false, params: [].concat(...[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].map((n) => KS.map((k) => ({ n, k })))),
      g: (x, p) => Math.pow(x, p.n) * Math.exp(-p.k * x),
      value: (p) => S(mul([num(fact(p.n)), pow(kNode(p.k), num(-(p.n + 1)))])), where: (p) => 'n = ' + p.n + ',\\ a = ' + TX(kNode(p.k)) },
    { rule: 'boseInt', even: false, params: [{ n: 1 }, { n: 3 }], g: (x, p) => Math.pow(x, p.n) / Math.expm1(x),
      value: (p) => (p.n === 1 ? S(mul([num(1, 6), pow(piN(), num(2))])) : S(mul([num(1, 15), pow(piN(), num(4))]))), where: (p) => 'n = ' + p.n },
    { rule: 'lnSinInt', range: 'halfpi', params: [{ s: 'sin' }, { s: 'cos' }], g: (x, p) => Math.log(p.s === 'sin' ? Math.sin(x) : Math.cos(x)),
      value: () => S(mul([num(-1, 2), piN(), fn('ln', num(2))])) },
  ];
  function tryTable(ctx, a, b) {
    const f = ctx.fx;
    let mode = null;
    if (a.val === 0 && b.inf === 1) mode = 'pos';
    else if (a.inf === -1 && b.inf === 1) mode = 'all';
    else if (a.inf === -1 && b.val === 0) mode = 'neg';
    const halfpi = a.val === 0 && !b.inf && Math.abs(b.val - PI / 2) < 1e-12;
    for (const E of TABLE) {
      if (E.range === 'halfpi' ? !halfpi : !mode || (mode !== 'pos' && !E.even)) continue;
      const xs = E.range === 'halfpi' ? [0.2, 0.5, 0.9, 1.2, 1.5] : [0.37, 0.81, 1.3, 1.9, 2.6, 3.3];
      for (const p of E.params) {
        const g0 = E.g(xs[0], p), f0 = f(xs[0]);
        if (!g0 || !isFinite(f0)) continue;
        const c = f0 / g0;
        if (!xs.every((x) => Math.abs(f(x) - c * E.g(x, p)) <= 1e-9 * (1 + Math.abs(f(x))))) continue;
        if (mode !== 'pos' && E.range !== 'halfpi' && !parity(f, Infinity, 1)) continue;
        const cr = ratApprox(c, 200, 1e-11);
        const cN = cr ? num(cr[0], cr[1]) : recognize(c);
        if (!cN) continue;
        const base = E.value(p);
        const half = S(mul([cN, base]));
        const zero = { inf: 0, val: 0, tex: '0', node: ZERO };
        const lhsHalf = intAB(ctx.f, ctx.v, mode === 'neg' || mode === 'all' ? zero : a, mode === 'neg' ? { tex: '\\infty' } : mode === 'all' ? b : b);
        const tStep = {
          lhsTex: lhsHalf, rules: [E.rule], children: [], formula: stmt(E.rule), where: E.where ? E.where(p) : '',
          combinedTex: isOneN(cN) ? null : TX(cN) + ' \\cdot ' + paren(TX(base)), resultTex: TX(half),
        };
        if (mode === 'pos' || E.range === 'halfpi') return { step: tStep, value: half, method: 'table' };
        const val = mode === 'all' ? S(mul([num(2), half])) : half;
        const step = {
          lhsTex: intAB(ctx.f, ctx.v, a, b), rules: ['intEvenSym'], children: [tStep], formula: stmt('intEvenSym'),
          note: { label: 'Even', tex: 'f(-' + tex(V(ctx.v)) + ') = f(' + tex(V(ctx.v)) + ')' },
          setup: (mode === 'all' ? '2' : '') + lhsHalf, resultTex: TX(val),
        };
        return { step, value: val, method: 'table' };
      }
    }
    return null;
  }
  const isOneN = (n) => n.type === 'num' && n.n === 1 && n.d === 1;
  const paren = (t) => '\\left(' + t + '\\right)';

  /* ---------------- solving on a < b ---------------- */
  const close = (x, y) => Math.abs(x - y) <= 1e-6 * Math.max(1, Math.abs(y));
  function solve(ctx, a, b) {
    const { fx, v } = ctx;
    const [wl, wr] = windowOf(a.val, b.val);
    const sc = scan(fx, wl, wr);
    const sing = sc.sing.filter((p) => p.val > a.val && p.val < b.val);
    const endA = a.inf ? { inf: true } : endInfo(fx, a.val, 1);
    const endB = b.inf ? { inf: true } : endInfo(fx, b.val, -1);
    if (sc.gap) throw fail('The integrand is not a real number on part of this interval, so the integral is undefined there.', { undefinedRegion: true });
    a = Object.assign({}, a, { improper: !!(endA.undef || endA.blow) });
    b = Object.assign({}, b, { improper: !!(endB.undef || endB.blow) });
    const improper = !!(a.inf || b.inf || sing.length || a.improper || b.improper);
    const qr = quadPieces(fx, [a].concat(sing, [b]));
    const lhs = intAB(ctx.f, v, a, b);
    const meta = { improper, sing, quad: qr };

    // 1. odd symmetry
    if (!a.inf !== !b.inf ? false : a.inf ? a.inf === -b.inf : Math.abs(a.val + b.val) <= 1e-12 * Math.max(1, Math.abs(b.val))) {
      if (parity(fx, b.val, -1)) {
        const half = quad(fx, 0, b.val);
        if (!sing.length && !b.improper && half.ok) {
          const vt = tex(V(v));
          return Object.assign(meta, {
            step: { lhsTex: lhs, rules: ['intOddSym'], children: [], formula: stmt('intOddSym'),
              note: { label: 'Odd', tex: 'f(-' + vt + ') = -f(' + vt + ')' }, resultTex: '0' },
            value: ZERO, approx: 0, divergent: 0, method: 'symmetry',
          });
        }
      }
    }
    // 2. Fundamental Theorem of Calculus
    const ftc = tryFTC(ctx, a, b, sing);
    if (ftc) {
      if (ftc.divergent && !qr.ok) return Object.assign(meta, ftc, { improper: true });
      if (!ftc.divergent && (!qr.ok || close(ftc.approx, qr.val))) return Object.assign(meta, ftc, { improper });
    }
    // 3. famous results
    if (!ctx.consts.length) {
      const tb = tryTable(ctx, a, b);
      if (tb && (!qr.ok || close(evaluate(tb.value, {}), qr.val))) return Object.assign(meta, tb, { approx: evaluate(tb.value, {}), divergent: 0 });
    }
    // 4. numbers
    if (ctx.consts.length) throw fail('With letters like ' + ctx.consts.join(', ') + ' in the integrand, only exact answers are possible, and none was found.');
    const why = ctx.nonElem ? 'No elementary antiderivative, so the value is computed numerically.' : 'No antiderivative was found, so the value is computed numerically.';
    if (qr.ok) {
      const guess = recognize(qr.val, 1e-11, 24);
      return Object.assign(meta, {
        step: { lhsTex: lhs, rules: improper ? ['numericInt', 'improperDef'] : ['numericInt'], children: [], formula: stmt('numericInt'),
          note: { label: 'Estimate', tex: '\\text{double-exponential quadrature, error} \\lesssim ' + fmtNum(Math.max(qr.err, 1e-12 * Math.max(1, Math.abs(qr.val))), 1) },
          caption: why, rel: '\\approx', resultTex: fmtNum(qr.val) },
        value: null, approx: qr.val, err: qr.err, divergent: 0, method: 'numeric', guess, why,
      });
    }
    if (improper) {
      return Object.assign(meta, {
        step: { lhsTex: lhs, rules: ['numericInt', 'improperDef'], children: [], formula: stmt('improperDef'),
          note: { label: 'Estimate', tex: '\\text{the numerical estimates do not settle down}' }, resultTex: '\\text{diverges}' },
        value: null, approx: null, divergent: 'osc', method: 'numeric', why: 'The numerical estimates do not settle down, so this improper integral appears to diverge.',
      });
    }
    throw fail('Could not evaluate this integral exactly or numerically.');
  }

  function rulesUsed(step, out) {
    out = out || [];
    step.rules.forEach((r) => { if (!out.includes(r)) out.push(r); });
    (step.children || []).forEach((c) => rulesUsed(c, out));
    return out;
  }

  function definite(tree, v, loSrc, hiSrc) {
    v = v || 'x';
    const old = Calc.getVar ? Calc.getVar() : 'x';
    Calc.setVar(v);
    try { return run(tree, v, loSrc, hiSrc); } finally { Calc.setVar(old); }
  }
  function run(tree, v, loSrc, hiSrc) {
    let lo, hi;
    try { lo = parseBound(loSrc, v); } catch (e) { throw fail('Lower limit: ' + e.message, { bound: 'lo' }); }
    try { hi = parseBound(hiSrc, v); } catch (e) { throw fail('Upper limit: ' + e.message, { bound: 'hi' }); }
    const f = S(tree);
    const consts = Array.from(Calc.freeVars(f)).filter((x) => x !== v);
    const env = constEnv(consts), env2 = constEnv(consts, true);
    const ctx = { f, v, env, env2, consts, fx: makeF(f, env, v) };
    let out;
    if (lo.inf && lo.inf === hi.inf) throw fail('Both limits are the same infinity, so there is no interval to integrate over.');
    if (!lo.inf && !hi.inf && Math.abs(lo.val - hi.val) <= 1e-14 * Math.max(1, Math.abs(lo.val))) {
      out = { step: { lhsTex: intAB(f, v, lo, hi), rules: ['intProps'], children: [], formula: '\\int_{a}^{a} f(x)\\,dx = 0', resultTex: '0' },
        value: ZERO, approx: 0, divergent: 0, method: 'equal', improper: false, sing: [] };
    } else if (lo.val > hi.val) {
      const inner = solve(ctx, hi, lo);
      const value = inner.value ? S(mul([NEG1, inner.value])) : null;
      const divergent = typeof inner.divergent === 'number' ? -inner.divergent : inner.divergent;
      const resTex = divergent ? divTex(divergent) : value ? TX(value) : '\\approx ' + fmtNum(-inner.approx);
      out = Object.assign({}, inner, {
        step: { lhsTex: intAB(f, v, lo, hi), rules: ['intProps'], children: [Object.assign({}, inner.step, { caption: 'Swap the limits' })],
          formula: '\\int_{a}^{b} f(x)\\,dx = -\\int_{b}^{a} f(x)\\,dx', setup: '-' + intAB(f, v, hi, lo), resultTex: resTex },
        value, divergent, approx: inner.approx === null ? null : -inner.approx, guess: inner.guess ? S(mul([NEG1, inner.guess])) : null,
      });
    } else {
      out = solve(ctx, lo, hi);
    }
    // "≈ 0.74" results: the step prints "∫ … ≈ 0.74" instead of "= ≈ 0.74"
    const relFix = (st) => {
      if (/^\\approx /.test(st.resultTex || '')) { st.rel = '\\approx'; st.resultTex = st.resultTex.slice(8); }
      (st.children || []).forEach(relFix);
    };
    relFix(out.step);
    const resultTex = out.divergent ? divTex(out.divergent) : out.value ? TX(out.value) : null;
    return {
      definite: true, steps: [out.step], result: out.value || null, resultTex, approx: out.approx, approxTex: out.approx === null || out.approx === undefined ? null : fmtNum(out.approx),
      err: out.err, guess: out.guess || null, guessTex: out.guess ? TX(out.guess) : null, why: out.why || null,
      method: out.method, rules: rulesUsed(out.step), divergent: out.divergent || 0, improper: !!out.improper,
      antideriv: out.antideriv || null, lo, hi, consts,
      plot: { sing: (out.sing || []).map((p) => p.val), consts: consts.length > 0 },
    };
  }

  Object.assign(Calc, { definite, parseBound, BoundError, quadrature: quad, recognizeNumber: recognize });
})(typeof window !== 'undefined' ? window : globalThis);
