/* integrate.js — step-tracing symbolic integrator (indefinite integrals).
 *
 * integrate(tree, v) returns { steps:[Step], result, resultTex, rules, check } or throws IntegrationError.
 * A Step has the same shape as the differentiator's (see derive.js), plus:
 *   lhsTex – the integral being evaluated, e.g. "\int x e^{x}\,dx"
 *   note   – a rewrite shown before the work ({ label, tex })
 *   back   – a back-substitution note shown after the sub-steps
 *
 * Strategy order (first that works wins; every candidate answer is checked by
 * differentiating numerically and comparing with the integrand):
 *   constant · sum · constant multiple · table of common integrals (with linear inner argument) ·
 *   g'/g · rational functions (long division, partial fractions, linear-over-quadratic) ·
 *   expansion · completing the square · trig powers / half-angle / reduction / product-to-sum ·
 *   u-substitution · trig substitution · integration by parts (LIATE, with the cyclic case). */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const { num, C, V, add, mul, div, pow, neg, fn, TEX, tex, key, contains, isNum, isZero, isOne, isInt, numEq,
    radd, rmul, rneg, rinv, evaluate, paren } = Calc;

  class IntegrationError extends Error {}

  const ONE = num(1), ZERO = num(0), NEG1 = num(-1), TWO = num(2), HALF = num(1, 2);
  const MAXD = 6;          // depth budget for the expensive strategies (u-sub, parts, trig sub)
  const CALL_LIMIT = 6000;  // overall search budget
  const TIME_LIMIT = 2500;  // ms

  let X = 'x';
  let memo = new Map(), busy = new Set(), calls = 0, deadline = 0, CENV = {};

  const S = (n) => Calc.simplify(n);
  const P = (n) => Calc.present(n);
  const T = (n) => tex(P(n));
  const XV = () => V(X);
  const isC = (n) => !contains(n, X);
  const facs = (n) => (n.type === 'mul' ? n.factors : [n]);
  const prod = (a) => (a.length === 0 ? ONE : a.length === 1 ? a[0] : S(mul(a)));
  const powOf = (n) => (n.type === 'pow' ? { b: n.base, e: n.exp } : { b: n, e: ONE });
  const sub = (a, b) => add([a, neg(b)]);
  const inv = (a) => pow(a, NEG1);
  const sq = (a) => pow(a, TWO);
  const vt = (v) => tex(V(v || X));
  const stmt = (id) => (Calc.RULE_BY_ID && Calc.RULE_BY_ID[id] ? Calc.RULE_BY_ID[id].statement : '');
  const bare = (t) => t.replace(/ \\cdot /g, '');

  function withVar(v, f) {
    const old = X;
    X = v; Calc.setVar(v);
    try { return f(); } finally { X = old; Calc.setVar(old); }
  }

  /* ---------------- tree utilities ---------------- */
  function mapKids(n, g) {
    switch (n.type) {
      case 'add': return add(n.terms.map(g));
      case 'mul': return mul(n.factors.map(g));
      case 'pow': return pow(g(n.base), g(n.exp));
      case 'func': return n.base ? fn(n.name, g(n.arg), g(n.base)) : fn(n.name, g(n.arg));
      case 'neg': return neg(g(n.arg));
      case 'div': return div(g(n.num), g(n.den));
      default: return n;
    }
  }
  const replaceVar = (n, name, t) => (n.type === 'var' ? (n.name === name ? t : n) : mapKids(n, (c) => replaceVar(c, name, t)));
  const fresh = (n) => S(replaceVar(n, '\u0000', null)); // rebuild every node so it is re-canonicalised under the current variable

  // a variable name not used in `n` (for u, w, θ …)
  function freshName(n, prefs) {
    const used = Calc.freeVars(n);
    used.add(X);
    return prefs.find((p) => !used.has(p)) || 'w';
  }

  function constEnv(n) {
    const vals = { a: 1.37, b: 0.73, c: 2.11, k: 1.61, m: 1.29, n: 2.3, p: 0.83, q: 1.17, r: 1.43, s: 0.91 };
    const env = {};
    Calc.freeVars(n).forEach((v) => { env[v] = vals[v] || 1.19; });
    return env;
  }
  const sgn = (n) => { const v = evaluate(n, CENV); return isFinite(v) ? Math.sign(v) : 0; };

  /* ---------------- sign facts (for ln|u|) ---------------- */
  function nonneg(n) {
    if (isNum(n)) return n.n >= 0;
    if (n.type === 'const') return true;
    if (n.type === 'func') return n.name === 'abs' || n.name === 'cosh' || n.name === 'sech' || n.name === 'exp';
    if (n.type === 'pow') {
      if (n.base.type === 'const' || (isNum(n.base) && n.base.n > 0)) return true;
      if (isNum(n.exp) && !n.exp.f && n.exp.n % 2 === 0) return true;
      if (isNum(n.exp) && !n.exp.f && n.exp.d % 2 === 0) return true; // even root
      return nonneg(n.base);
    }
    if (n.type === 'mul') return n.factors.every(nonneg);
    if (n.type === 'add') return n.terms.every(nonneg);
    return false;
  }
  const absS = (u) => (nonneg(S(u)) ? u : fn('abs', u));
  const lnAbs = (u) => fn('ln', absS(u));

  /* ---------------- polynomials ---------------- */
  // coefficients (canonical trees, constant in X) of a polynomial in X, or null
  function polyC(n) {
    if (isC(n)) return [n];
    const padd = (a, b) => {
      const out = [];
      for (let i = 0; i < Math.max(a.length, b.length); i++) out.push(S(add([a[i] || ZERO, b[i] || ZERO])));
      return out;
    };
    const pmul = (a, b) => {
      const out = Array(a.length + b.length - 1).fill(ZERO);
      a.forEach((x, i) => b.forEach((y, j) => { out[i + j] = S(add([out[i + j], mul([x, y])])); }));
      return out;
    };
    const trim = (a) => { a = a.slice(); while (a.length > 1 && isZero(a[a.length - 1])) a.pop(); return a; };
    switch (n.type) {
      case 'var': return [ZERO, ONE];
      case 'add': {
        let acc = [ZERO];
        for (const t of n.terms) { const p = polyC(t); if (!p) return null; acc = padd(acc, p); }
        return trim(acc);
      }
      case 'mul': {
        let acc = [ONE];
        for (const f of n.factors) { const p = polyC(f); if (!p) return null; acc = pmul(acc, p); }
        return trim(acc);
      }
      case 'pow': {
        if (!isInt(n.exp) || n.exp.n < 0 || n.exp.n > 12) return null;
        const p = polyC(n.base);
        if (!p) return null;
        let acc = [ONE];
        for (let i = 0; i < n.exp.n; i++) acc = pmul(acc, p);
        return trim(acc);
      }
    }
    return null;
  }
  function lin(u) {
    if (isC(u)) return null;
    const p = polyC(u);
    if (!p || p.length !== 2) return null;
    return { a: p[1], b: p[0] };
  }
  const isX = (u) => u.type === 'var' && u.name === X;

  // exact rational polynomials: arrays of num nodes, lowest degree first
  const R0 = ZERO, R1 = ONE;
  function ratCoeffs(n) {
    const p = polyC(n);
    if (!p || !p.every((c) => isNum(c) && !c.f)) return null;
    return p;
  }
  const rtrim = (a) => { a = a.slice(); while (a.length > 1 && isZero(a[a.length - 1])) a.pop(); return a; };
  function padd(a, b) {
    const out = [];
    for (let i = 0; i < Math.max(a.length, b.length); i++) out.push(radd(a[i] || R0, b[i] || R0));
    return rtrim(out);
  }
  function pmul(a, b) {
    const out = Array(a.length + b.length - 1).fill(R0);
    a.forEach((x, i) => b.forEach((y, j) => { out[i + j] = radd(out[i + j], rmul(x, y)); }));
    return rtrim(out);
  }
  const pscale = (a, c) => rtrim(a.map((x) => rmul(x, c)));
  function ppow(a, k) { let r = [R1]; for (let i = 0; i < k; i++) r = pmul(r, a); return r; }
  function pdivmod(a, b) {
    a = rtrim(a); b = rtrim(b);
    const db = b.length - 1, lead = b[db];
    const r = a.slice();
    const q = Array(Math.max(a.length - db, 1)).fill(R0);
    for (let i = r.length - 1; i >= db; i--) {
      const c = rmul(r[i], rinv(lead));
      q[i - db] = c;
      for (let j = 0; j <= db; j++) r[i - db + j] = radd(r[i - db + j], rneg(rmul(c, b[j])));
    }
    return { q: rtrim(q), r: rtrim(db === 0 ? [R0] : r.slice(0, db)) };
  }
  const peval = (a, x) => a.reduceRight((s, c) => radd(rmul(s, x), c), R0);
  const pzero = (a) => a.every(isZero);
  const polyTree = (a) => S(add(a.map((c, i) => mul([c, pow(XV(), num(i))]))));

  function ratSqrt(r) {
    if (r.f || r.n < 0) return null;
    const a = Math.round(Math.sqrt(r.n)), b = Math.round(Math.sqrt(r.d));
    return a * a === r.n && b * b === r.d ? num(a, b) : null;
  }
  function findRoot(R) {
    let L = 1;
    for (const c of R) { if (c.f) return null; L = (L / Calc.gcd(L, c.d)) * c.d; if (!Number.isSafeInteger(L)) return null; }
    const ints = R.map((c) => c.n * (L / c.d));
    const a0 = Math.abs(ints[0]), an = Math.abs(ints[ints.length - 1]);
    if (!a0 || a0 > 1e6 || an > 1e6) return null;
    const divs = (n) => { const out = []; for (let i = 1; i * i <= n; i++) if (n % i === 0) { out.push(i); if (i * i !== n) out.push(n / i); } return out; };
    for (const p of divs(a0)) for (const q of divs(an)) for (const s of [1, -1]) {
      const r = num(s * p, q);
      if (isZero(peval(R, r))) return r;
    }
    return null;
  }
  // D = lc · Π (x − r)^m · Π q^m  (q monic quadratics without rational roots), or null
  function factorPoly(D) {
    D = rtrim(D);
    const lc = D[D.length - 1];
    let R = pscale(D, rinv(lc));
    const lins = [];
    const addRoot = (r) => { const e = lins.find((l) => l.r.n === r.n && l.r.d === r.d); if (e) e.m++; else lins.push({ r, m: 1 }); };
    for (let guard = 0; R.length > 1 && guard < 40; guard++) {
      if (isZero(R[0])) { addRoot(R0); R = R.slice(1); continue; }
      const r = findRoot(R);
      if (!r) break;
      addRoot(r);
      R = pdivmod(R, [rneg(r), R1]).q;
    }
    const quads = [];
    const d = R.length - 1;
    if (d === 2) quads.push({ q: R, m: 1 });
    else if (d === 4) {
      // perfect square of a quadratic?
      const p = rmul(R[3], HALF), t = rmul(radd(R[2], rneg(rmul(p, p))), HALF);
      const s = [t, p, R1];
      if (pzero(padd(pmul(s, s), pscale(R, NEG1)))) quads.push({ q: s, m: 2 });
      else if (isZero(R[1]) && isZero(R[3])) {
        // x⁴ + c2 x² + c0
        const c2 = R[2], c0 = R[0];
        const disc = radd(rmul(c2, c2), rmul(num(-4), c0));
        const sd = ratSqrt(disc);
        if (sd) {
          const y1 = rmul(radd(rneg(c2), sd), HALF), y2 = rmul(radd(rneg(c2), rneg(sd)), HALF);
          quads.push({ q: [rneg(y1), R0, R1], m: 1 }, { q: [rneg(y2), R0, R1], m: 1 });
        } else {
          // (x² + s x + t)(x² − s x + t) with t² = c0, s² = 2t − c2
          const t0 = ratSqrt(c0);
          let done = false;
          if (t0) for (const t1 of [t0, rneg(t0)]) {
            const s2 = radd(rmul(TWO, t1), rneg(c2)), s1 = ratSqrt(s2);
            if (s1 && !isZero(s1)) { quads.push({ q: [t1, s1, R1], m: 1 }, { q: [t1, rneg(s1), R1], m: 1 }); done = true; break; }
          }
          if (!done) return null;
        }
      } else return null;
    } else if (d !== 0) return null;
    return { lc, lins, quads };
  }
  function solveLinear(M, rhs) {
    const n = rhs.length;
    const A = M.map((row, i) => row.concat([rhs[i]]));
    for (let c = 0; c < n; c++) {
      let p = c;
      while (p < n && isZero(A[p][c])) p++;
      if (p === n) return null;
      [A[c], A[p]] = [A[p], A[c]];
      const iv = rinv(A[c][c]);
      A[c] = A[c].map((x) => rmul(x, iv));
      for (let r = 0; r < n; r++) {
        if (r === c || isZero(A[r][c])) continue;
        const f = A[r][c];
        A[r] = A[r].map((x, j) => radd(x, rneg(rmul(f, A[c][j]))));
      }
    }
    return A.map((r) => r[n]);
  }

  /* ---------------- answer checking ---------------- */
  const PTS = [0.37, 1.21, -0.63, 2.07, -1.48, 0.83, 2.9, -2.35, 0.13, -0.21, 0.55, 1.67, 3.7, -3.1, 0.051, -0.047, 4.6, 6.3];
  function verify(f, F, posOnly) {
    const env = Object.assign({}, CENV);
    let good = 0, any = false;
    for (const x of PTS) {
      if (posOnly && x <= 0) continue;
      env[X] = x;
      const fx = evaluate(f, env);
      if (!isFinite(fx) || Math.abs(fx) > 1e7) continue;
      any = true;
      const h = 1e-5 * Math.max(1, Math.abs(x));
      env[X] = x + h; const F1 = evaluate(F, env);
      env[X] = x - h; const F2 = evaluate(F, env);
      if (!isFinite(F1) || !isFinite(F2)) continue;
      const d = (F1 - F2) / (2 * h);
      const tol = 1e-5 * Math.max(1, Math.abs(fx)) + 1e-10 * Math.max(Math.abs(F1), Math.abs(F2)) / h;
      if (!(Math.abs(d - fx) <= tol)) return false;
      if (++good >= 7) break;
    }
    return good > 0 || !any;
  }

  /* ---------------- steps ---------------- */
  function intTex(f, v) {
    const p = P(f);
    let t = tex(p);
    if (p.type === 'add') t = paren(t);
    return '\\int ' + t + '\\,d' + vt(v);
  }
  const INT = (f, v) => TEX(intTex(f, v));
  // label a sub-step (a copy, since steps are shared through the memo)
  const cap = (st, caption) => Object.assign({}, st, { caption });
  function mk(f) {
    return { expr: f, exprTex: T(f), lhsTex: intTex(f), v: X, rules: [], children: [] };
  }
  // √c for a constant: pulls out square factors (√(3/4) = √3/2) and treats symbols as positive (√(a²) = a)
  function sqrtC(c) {
    c = S(c);
    if (isNum(c) && !c.f && c.n > 0) {
      const split = (n) => { let out = 1, rest = n; for (let k = 2; k * k <= rest; k++) while (rest % (k * k) === 0) { rest /= k * k; out *= k; } return [out, rest]; };
      const [on, rn] = split(c.n * c.d); // √(n/d) = √(n·d)/d
      return S(mul([num(on, c.d), pow(num(rn), HALF)]));
    }
    if (c.type === 'pow' && isInt(c.exp) && c.exp.n % 2 === 0 && c.base.type === 'var') return S(pow(c.base, num(c.exp.n / 2)));
    return S(pow(c, HALF));
  }
  // (x + 1/2)·(2/√3) → (2x + 1)/√3 : clear rational denominators inside a sum factor
  function clearFrac(n) {
    if (n.type !== 'mul') return n;
    const ai = n.factors.findIndex((f) => f.type === 'add');
    if (ai < 0 || n.factors.some((f, i) => i !== ai && !isC(f))) return n;
    const A = n.factors[ai];
    let L = 1;
    for (const t of A.terms) {
      const c = isNum(t) ? t : t.type === 'mul' && isNum(t.factors[0]) ? t.factors[0] : ONE;
      if (c.f) return n;
      L = (L / Calc.gcd(L, c.d)) * c.d;
    }
    if (L === 1) return n;
    const A2 = S(add(A.terms.map((t) => mul([num(L), t]))));
    return S(mul([A2, num(1, L)].concat(n.factors.filter((_, i) => i !== ai))));
  }
  function tidyArgs(n) {
    if (n.type === 'func') {
      if (n.name === 'atan' && n.arg.type === 'func' && n.arg.name === 'tan') return n.arg.arg; // same derivative
      const a = clearFrac(tidyArgs(n.arg));
      return a === n.arg ? n : S(fn(n.name, a, n.base));
    }
    if (['add', 'mul', 'pow'].includes(n.type)) {
      const kids = Calc.children(n), nk = kids.map(tidyArgs);
      if (nk.every((k, i) => k === kids[i])) return n;
      return S(n.type === 'add' ? add(nk) : n.type === 'mul' ? mul(nk) : pow(nk[0], nk[1]));
    }
    return n;
  }
  function tidy(F) {
    F = tidyArgs(S(F));
    if (F.type === 'mul' && F.factors.length === 2 && isNum(F.factors[0]) && F.factors[1].type === 'add') return S(add([F]));
    return F;
  }
  function done(st, F, combinedTex) {
    st.result = tidy(F);
    st.resultTex = Calc.texOf(st.result);
    if (combinedTex && bare(combinedTex) !== bare(st.resultTex)) st.combinedTex = combinedTex;
    return st;
  }
  // negative leading coefficient → the positive version, else null
  function negLead(t) {
    if (isNum(t) && t.n < 0) return rneg(t);
    if (t.type === 'mul' && isNum(t.factors[0]) && t.factors[0].n < 0) return S(mul([NEG1, t]));
    return null;
  }
  // display a sum of signed pieces
  const signedSum = (parts, g) => add(parts.map((p, i) => (p.s < 0 ? neg(g(p, i)) : g(p, i))));

  /* ---------------- core search ---------------- */
  function I(f, d) {
    f = S(f);
    const k = X + '|' + key(f);
    const m = memo.get(k);
    if (m) { if (m.st) return m.st; if (m.d >= d) return null; }
    if (busy.has(k)) return null;
    if (++calls > CALL_LIMIT || Date.now() > deadline) return null;
    busy.add(k);
    let st = null;
    try { st = attempt(f, d); } finally { busy.delete(k); }
    memo.set(k, st ? { st } : { d });
    return st;
  }
  const STRATS = [sConstant, sSum, sConstMult, sTable, sLogDeriv, sRational, sExpandEarly, sCompleteSquare, sTrig, sUSub, sExpand, sTrigSub, sParts, sUSubLn, sWeierstrass];
  function attempt(f, d) {
    for (const strat of STRATS) {
      let st = null;
      try { st = strat(f, d); } catch (e) { if (e instanceof IntegrationError) throw e; st = null; }
      if (st && verify(f, st.result, st.posOnly)) return st;
    }
    return null;
  }

  /* 1. constant */
  function sConstant(f) {
    if (!isC(f)) return null;
    const st = mk(f);
    st.rules = ['intConstant'];
    st.formula = '\\int c\\,d' + vt() + ' = c' + vt();
    return done(st, mul([f, XV()]));
  }

  /* 2. sum and difference */
  function sSum(f, d) {
    if (f.type !== 'add') return null;
    const parts = f.terms.map((t) => { const m = negLead(t); return m ? { s: -1, t: m } : { s: 1, t }; });
    const kids = [];
    for (const p of parts) { const c = I(p.t, d); if (!c) return null; kids.push(c); }
    const st = mk(f);
    st.rules = ['intSum'];
    st.formula = '\\int (f \\pm g)\\,d' + vt() + ' = \\int f\\,d' + vt() + ' \\pm \\int g\\,d' + vt();
    st.setup = tex(signedSum(parts, (p) => INT(p.t)));
    st.children = kids;
    const combined = tex(signedSum(parts, (p, i) => P(kids[i].result)));
    return done(st, signedSum(parts, (p, i) => kids[i].result), combined);
  }

  /* 3. constant multiple */
  function sConstMult(f, d) {
    const fs = facs(f);
    const cs = fs.filter(isC);
    if (!cs.length || cs.length === fs.length) return null;
    const c = prod(cs), r = prod(fs.filter((x) => !isC(x)));
    const kid = I(r, d);
    if (!kid) return null;
    const st = mk(f);
    st.rules = ['intConstMult'];
    st.formula = '\\int c\\,f\\,d' + vt() + ' = c\\int f\\,d' + vt();
    st.where = 'c = ' + T(c);
    st.setup = tex(mul([P(c), INT(r)]));
    st.children = [kid];
    return done(st, mul([c, kid.result]), tex(mul([P(c), P(kid.result)])));
  }

  /* 4. table of common integrals */
  const FN_TABLE = {
    sin: ['intSin', (u) => neg(fn('cos', u))],
    cos: ['intCos', (u) => fn('sin', u)],
    tan: ['intTan', (u) => lnAbs(fn('sec', u))],
    cot: ['intCot', (u) => lnAbs(fn('sin', u))],
    sec: ['intSec', (u) => lnAbs(add([fn('sec', u), fn('tan', u)]))],
    csc: ['intCsc', (u) => neg(lnAbs(add([fn('csc', u), fn('cot', u)])))],
    sinh: ['intSinh', (u) => fn('cosh', u)],
    cosh: ['intCosh', (u) => fn('sinh', u)],
    tanh: ['intTanh', (u) => fn('ln', fn('cosh', u))],
    coth: ['intCoth', (u) => lnAbs(fn('sinh', u))],
    sech: ['intSech', (u) => fn('atan', fn('sinh', u))],
    csch: ['intCsch', (u) => lnAbs(fn('tanh', mul([HALF, u])))],
  };
  const SQ_TABLE = {
    sec: ['intSec2', (u) => fn('tan', u)],
    csc: ['intCsc2', (u) => neg(fn('cot', u))],
    sech: ['intSech2', (u) => fn('tanh', u)],
    csch: ['intCsch2', (u) => neg(fn('coth', u))],
  };
  const PAIR_TABLE = [
    ['sec', 'tan', 'intSecTan', (u) => fn('sec', u)],
    ['csc', 'cot', 'intCscCot', (u) => neg(fn('csc', u))],
    ['sech', 'tanh', 'intSechTanh', (u) => neg(fn('sech', u))],
    ['csch', 'coth', 'intCschCoth', (u) => neg(fn('csch', u))],
  ];

  // integrand = shape(u) with u linear in X → { rule, u, G(u) }
  function matchSimple(r) {
    const { b, e } = powOf(r);
    if (isC(e) && !isC(b) && lin(b)) {
      if (numEq(e, -1)) return { rule: 'intRecip', u: b, G: (u) => lnAbs(u) };
      const e1 = S(add([e, ONE]));
      return { rule: 'intPower', u: b, G: (u) => mul([pow(u, e1), inv(e1)]) };
    }
    if (isC(b) && !isC(e) && lin(e)) {
      if (b.type === 'const' && b.name === 'e') return { rule: 'intExp', u: e, G: (u) => pow(C('e'), u) };
      return { rule: 'intExpA', u: e, G: (u) => mul([pow(b, u), inv(fn('ln', b))]) };
    }
    if (r.type === 'func' && r.name === 'abs' && lin(r.arg)) return { rule: 'intAbs', u: r.arg, G: (u) => mul([HALF, u, fn('abs', u)]) };
    if (r.type === 'func' && FN_TABLE[r.name] && lin(r.arg)) {
      const [rule, G] = FN_TABLE[r.name];
      return { rule, u: r.arg, G };
    }
    if (r.type === 'pow' && numEq(e, 2) && b.type === 'func' && SQ_TABLE[b.name] && lin(b.arg)) {
      const [rule, G] = SQ_TABLE[b.name];
      return { rule, u: b.arg, G };
    }
    if (r.type === 'mul' && r.factors.length === 2) {
      const [f1, f2] = r.factors;
      if (f1.type === 'func' && f2.type === 'func' && key(f1.arg) === key(f2.arg) && lin(f1.arg)) {
        for (const [a, c, rule, G] of PAIR_TABLE) {
          if ((f1.name === a && f2.name === c) || (f1.name === c && f2.name === a)) return { rule, u: f1.arg, G };
        }
      }
    }
    return null;
  }
  // p + q x² (no linear term)
  function quadPQ(Q) {
    if (Q.type !== 'add') return null;
    const p = polyC(Q);
    if (!p || p.length !== 3 || !isZero(p[1]) || isZero(p[0])) return null;
    return { p: p[0], q: p[2] };
  }
  // the a²±x² family, inner argument x itself → { rule, F }
  function matchQuad(r) {
    const x = XV();
    const fs = facs(r);
    if (fs.length === 1) {
      const { b, e } = powOf(r);
      const pq = quadPQ(b);
      if (!pq) return null;
      const { p, q } = pq;
      const sp = sgn(p), sq_ = sgn(q);
      if (!sp || !sq_) return null;
      if (numEq(e, -1)) {
        if (sp === sq_) {
          const s = sp > 0 ? ONE : NEG1;
          const pp = sp > 0 ? p : S(neg(p)), qq = sp > 0 ? q : S(neg(q));
          const a = sqrtC(div(pp, qq));
          return { rule: 'intAtanForm', F: mul([s, inv(qq), inv(a), fn('atan', mul([x, inv(a)]))]) };
        }
        const k = sp > 0 ? inv(neg(q)) : neg(inv(q));
        const a2 = S(sp > 0 ? div(p, neg(q)) : div(neg(p), q));
        if (isNum(a2) && ratSqrt(a2)) return null; // rational roots: partial fractions read better
        const a = sqrtC(a2);
        return { rule: 'intAtanhForm', F: mul([k, inv(mul([TWO, a])), lnAbs(S(mul([add([a, x]), inv(sub(a, x))])))]) };
      }
      if (numEq(e, -1, 2)) {
        if (sp > 0 && sq_ < 0) {
          const a = sqrtC(div(p, neg(q)));
          return { rule: 'intAsinForm', F: mul([pow(neg(q), num(-1, 2)), fn('asin', mul([x, inv(a)]))]) };
        }
        if (sq_ > 0) {
          const arg = add([x, pow(add([sq(x), div(p, q)]), HALF)]);
          return { rule: 'intAsinhForm', F: mul([pow(q, num(-1, 2)), sp > 0 ? fn('ln', arg) : lnAbs(arg)]) };
        }
      }
      return null;
    }
    if (fs.length === 2) {
      const xi = fs.findIndex((g) => g.type === 'pow' && isX(g.base) && numEq(g.exp, -1));
      if (xi < 0) return null;
      const o = fs[1 - xi];
      const { b, e } = powOf(o);
      const pq = quadPQ(b);
      if (!pq || !numEq(e, -1, 2)) return null;
      const { p, q } = pq;
      if (!(sgn(p) < 0 && sgn(q) > 0)) return null;
      const a = sqrtC(div(neg(p), q));
      return { rule: 'intAsecForm', F: mul([pow(q, num(-1, 2)), inv(a), fn('asec', mul([fn('abs', x), inv(a)]))]) };
    }
    return null;
  }
  function sTable(f) {
    const m = matchSimple(f);
    if (m) {
      const st = mk(f);
      st.formula = stmt(m.rule);
      if (isX(m.u)) {
        st.rules = [m.rule];
        return done(st, m.G(XV()));
      }
      // linear inner argument: u = a x + b, du = a dx
      const L = lin(m.u);
      const W = freshName(f, ['u', 'w', 't', 's']);
      const U = V(W);
      st.rules = [m.rule, 'intLinearSub'];
      st.where = vt(W) + ' = ' + T(m.u) + ',\\; d' + vt(W) + ' = ' + T(L.a) + '\\,d' + vt();
      const fu = withVar(W, () => fresh(replaceKey(f, m.u, U)));
      const ia = P(S(inv(L.a)));
      st.setup = tex(isOne(L.a) ? INT(fu, W) : mul([ia, INT(fu, W)]));
      const Gu = m.G(U);
      return done(st, mul([m.G(m.u), inv(L.a)]), tex(isOne(L.a) ? Gu : mul([ia, Gu])));
    }
    const q = matchQuad(f);
    if (q) {
      const st = mk(f);
      st.rules = [q.rule];
      st.formula = stmt(q.rule);
      return done(st, q.F);
    }
    return null;
  }
  function replaceKey(n, g, U) {
    const kg = key(g);
    const walk = (m) => (key(m) === kg ? U : mapKids(m, walk));
    return walk(n);
  }

  /* 5. ∫ g'/g = ln|g| */
  function sLogDeriv(f) {
    for (const fac of facs(f)) {
      const { b, e } = powOf(fac);
      if (!numEq(e, -1) || isC(b)) continue;
      const gp = Dc(b);
      if (!gp || isZero(gp)) continue;
      const k = S(mul([f, b, inv(gp)]));
      if (!isC(k)) continue;
      const st = mk(f);
      st.rules = ['intLogDeriv'];
      st.formula = stmt('intLogDeriv');
      st.where = 'g = ' + T(b) + ",\\; g' = " + T(gp);
      if (!isOne(k)) st.setup = tex(mul([P(k), TEX('\\int \\frac{' + T(gp) + '}{' + T(b) + '}\\,d' + vt())]));
      return done(st, mul([k, lnAbs(b)]));
    }
    return null;
  }

  /* 6. rational functions */
  function sRational(f, d) {
    const nf = [], df = [];
    for (const fac of facs(f)) {
      const { b, e } = powOf(fac);
      if (isInt(e) && e.n < 0 && !isC(b)) df.push(e.n === -1 ? b : pow(b, num(-e.n)));
      else nf.push(fac);
    }
    if (!df.length) return null;
    const denTree = prod(df), numTree = prod(nf);
    const N = ratCoeffs(numTree), D = ratCoeffs(denTree);
    if (!N || !D) return null;
    const dD = D.length - 1, dN = N.length - 1;
    if (dD < 1) return null;
    // long division
    if (dN >= dD) {
      const { q, r } = pdivmod(N, D);
      const g = S(add([polyTree(q), mul([polyTree(r), inv(denTree)])]));
      if (key(g) === key(f)) return null;
      const kid = I(g, d);
      if (!kid) return null;
      const st = mk(f);
      st.rules = ['polyDiv'];
      st.formula = stmt('polyDiv');
      st.note = { label: 'Divide', tex: tex(div(P(numTree), P(denTree))) + ' = ' + T(g) };
      st.setup = intTex(g);
      st.children = [kid];
      return done(st, kid.result);
    }
    if (dD === 1) return null;
    const fac = factorPoly(D);
    if (!fac) return null;
    const onlyQuad = !fac.lins.length && fac.quads.length === 1;
    if (onlyQuad && dN === 1) return linOverQuad(f, N, fac, d);
    if (onlyQuad && fac.quads[0].m === 1) return null;
    if (fac.lins.length === 1 && !fac.quads.length && fac.lins[0].m === 1) return null;
    const pieces = partialFractions(N, D, fac);
    if (!pieces || pieces.length < 2) return null;
    const parts = pieces.map((t) => { const m = negLead(t); return m ? { s: -1, t: m } : { s: 1, t }; });
    const kids = [];
    for (const p of parts) { const c = I(p.t, d); if (!c) return null; kids.push(c); }
    const st = mk(f);
    st.rules = ['partialFrac'];
    st.formula = stmt('partialFrac');
    st.where = 'Q(' + vt() + ') = ' + tex(factoredTex(fac));
    st.note = { label: 'Decompose', tex: tex(div(P(numTree), P(denTree))) + ' = ' + tex(signedSum(parts, (p) => P(p.t))) };
    st.setup = tex(signedSum(parts, (p) => INT(p.t)));
    st.children = kids;
    return done(st, signedSum(parts, (p, i) => kids[i].result), tex(signedSum(parts, (p, i) => P(kids[i].result))));
  }
  function factoredTex(fac) {
    const fs = [];
    if (!isOne(fac.lc)) fs.push(fac.lc);
    const pw = (b, m) => (m === 1 ? b : pow(b, num(m)));
    fac.lins.forEach((l) => fs.push(pw(P(S(add([XV(), rneg(l.r)]))), l.m)));
    fac.quads.forEach((q) => fs.push(pw(P(polyTree(q.q)), q.m)));
    return fs.length === 1 ? fs[0] : mul(fs);
  }
  function partialFractions(N, D, fac) {
    const iv = rinv(fac.lc);
    const Dm = pscale(D, iv), Nm = pscale(N, iv);
    const basis = [];
    for (const l of fac.lins) {
      const lp = [rneg(l.r), R1], lt = S(add([XV(), rneg(l.r)]));
      for (let j = 1; j <= l.m; j++) {
        const other = pdivmod(Dm, ppow(lp, j)).q;
        basis.push({ poly: other, mk: (c) => mul([c, pow(lt, num(-j))]) });
      }
    }
    for (const q of fac.quads) {
      const qt = polyTree(q.q);
      for (let j = 1; j <= q.m; j++) {
        const other = pdivmod(Dm, ppow(q.q, j)).q;
        basis.push({ poly: pmul(other, [R0, R1]), quad: j, qt, x: true });
        basis.push({ poly: other, quad: j, qt });
      }
    }
    const n = Dm.length - 1;
    if (basis.length !== n) return null;
    const M = [];
    for (let i = 0; i < n; i++) M.push(basis.map((b) => b.poly[i] || R0));
    const rhs = []; for (let i = 0; i < n; i++) rhs.push(Nm[i] || R0);
    const sol = solveLinear(M, rhs);
    if (!sol) return null;
    const pieces = [];
    for (let i = 0; i < basis.length; i++) {
      const b = basis[i];
      if (b.quad) {
        // pair (x-coefficient, constant) for the same q^j
        const bx = sol[i], c0 = sol[i + 1];
        i++;
        if (isZero(bx) && isZero(c0)) continue;
        pieces.push(S(mul([add([mul([bx, XV()]), c0]), pow(b.qt, num(-b.quad))])));
      } else if (!isZero(sol[i])) pieces.push(S(b.mk(sol[i])));
    }
    return pieces;
  }
  // (b x + c)/(lc·q^m), q irreducible: split into A·q'/q^m + rest/q^m
  function linOverQuad(f, N, fac, d) {
    const q = fac.quads[0].q, m = fac.quads[0].m;
    const A = rmul(N[1], HALF), rest = radd(N[0], rneg(rmul(A, q[1])));
    if (isZero(rest)) return null; // pure g'/g^m: u-substitution handles it
    const qt = polyTree(q), qp = polyTree([q[1], TWO]);
    const iv = rinv(fac.lc);
    const p1 = S(mul([rmul(A, iv), qp, pow(qt, num(-m))]));
    const p2 = S(mul([rmul(rest, iv), pow(qt, num(-m))]));
    const parts = [p1, p2].map((t) => { const mm = negLead(t); return mm ? { s: -1, t: mm } : { s: 1, t }; });
    const kids = [];
    for (const p of parts) { const c = I(p.t, d); if (!c) return null; kids.push(c); }
    const st = mk(f);
    st.rules = ['linOverQuad'];
    st.formula = stmt('linOverQuad');
    st.where = "q = " + T(qt) + ",\\; q' = " + T(qp);
    st.note = { label: 'Split', tex: T(f) + ' = ' + tex(signedSum(parts, (p) => P(p.t))) };
    st.setup = tex(signedSum(parts, (p) => INT(p.t)));
    st.children = kids;
    return done(st, signedSum(parts, (p, i) => kids[i].result), tex(signedSum(parts, (p, i) => P(kids[i].result))));
  }

  /* 7. expansion */
  function expandTerms(n) {
    if (n.type === 'add') {
      const out = [];
      for (const t of n.terms) { const r = expandTerms(t); if (!r) return null; out.push(...r); }
      return out;
    }
    const mulOut = (lists) => {
      let acc = [ONE];
      for (const ts of lists) {
        const nacc = [];
        for (const a of acc) for (const t of ts) nacc.push(S(mul([a, t])));
        if (nacc.length > 160) return null;
        acc = nacc;
      }
      return acc;
    };
    if (n.type === 'mul') {
      const lists = [];
      for (const f of n.factors) { const r = expandTerms(f); if (!r) return null; lists.push(r); }
      return mulOut(lists);
    }
    if (n.type === 'pow' && n.base.type === 'add' && isInt(n.exp) && n.exp.n >= 2 && n.exp.n <= 8) {
      const b = expandTerms(n.base);
      if (!b) return null;
      return mulOut(Array(n.exp.n).fill(b));
    }
    return [n];
  }
  const hasSumFactor = (f) => facs(f).some((g) => g.type === 'add' || (g.type === 'pow' && g.base.type === 'add' && isInt(g.exp) && g.exp.n >= 2));
  function expandStep(f, d) {
    if (!hasSumFactor(f)) return null;
    const ts = expandTerms(f);
    if (!ts) return null;
    const g = S(add(ts));
    if (key(g) === key(f) || g.type !== 'add') return null;
    const kid = I(g, d);
    if (!kid) return null;
    const st = mk(f);
    st.note = { label: 'Expand', tex: T(f) + ' = ' + T(g) };
    st.setup = intTex(g);
    st.children = [kid];
    return done(st, kid.result);
  }
  // early: polynomials, or a sum times powers of x (e.g. (x+1)/√x)
  function sExpandEarly(f, d) {
    const monoOK = facs(f).every((g) => g.type === 'add' || isC(g) || isX(powOf(g).b) && isC(powOf(g).e) ||
      (g.type === 'pow' && g.base.type === 'add' && isInt(g.exp) && g.exp.n >= 2 && Calc.isPoly(g.base)));
    if (!(Calc.isPoly(f) || monoOK)) return null;
    return expandStep(f, d);
  }
  function sExpand(f, d) { return expandStep(f, d); }

  /* 8. completing the square: (a x² + b x + c)^e */
  function sCompleteSquare(f, d) {
    const { b, e } = powOf(f);
    if (b.type !== 'add' || !isNum(e) || (isInt(e) && e.n >= 0)) return null;
    const p = ratCoeffs(b);
    if (!p || p.length !== 3 || isZero(p[1])) return null;
    const [a0, a1, a2] = p;
    const h = rmul(a1, rinv(rmul(TWO, a2)));
    const k = radd(a0, rneg(rmul(rmul(a1, a1), rinv(rmul(num(4), a2)))));
    if (isZero(k)) return null;
    const W = freshName(f, ['u', 'w', 't', 's']);
    const U = V(W);
    const g = withVar(W, () => S(pow(add([mul([a2, sq(U)]), k]), e)));
    const kid = withVar(W, () => I(g, d));
    if (!kid) return null;
    const shift = S(add([XV(), h]));
    const st = mk(f);
    st.rules = ['completeSquare'];
    st.formula = stmt('completeSquare');
    const sqd = pow(P(shift), TWO);
    st.note = { label: 'Complete the square', tex: T(b) + ' = ' + tex(add([isOne(a2) ? sqd : mul([a2, sqd]), k])) };
    st.where = vt(W) + ' = ' + T(shift) + ',\\; d' + vt(W) + ' = d' + vt();
    st.setup = intTex(g, W);
    st.children = [kid];
    const F = fresh(replaceVar(kid.result, W, shift));
    return done(st, F, tex(replaceVar(P(kid.result), W, P(shift))));
  }

  /* 9. trigonometric integrals */
  const TRIG6 = ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'];
  function binom(n, k) { let r = 1; for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i; return Math.round(r); }
  function trigParts(f) {
    const out = [];
    for (const fac of facs(f)) {
      const { b, e } = powOf(fac);
      if (b.type !== 'func' || !TRIG6.includes(b.name) || !isInt(e) || !lin(b.arg)) return null;
      out.push({ name: b.name, arg: b.arg, e: e.n });
    }
    return out;
  }
  function rewriteStep(f, g, rule, label, noteTex, d) {
    g = S(g);
    if (key(g) === key(f)) return null;
    const kid = I(g, d);
    if (!kid) return null;
    const st = mk(f);
    st.rules = [rule];
    st.formula = stmt(rule);
    st.note = { label, tex: noteTex };
    st.setup = intTex(g);
    st.children = [kid];
    return done(st, kid.result);
  }
  const expanded = (n) => { const ts = expandTerms(S(n)); return ts ? S(add(ts)) : S(n); };
  function sTrig(f, d) {
    const parts = trigParts(f);
    if (!parts || !parts.length) return null;
    const keys = new Set(parts.map((p) => key(p.arg)));
    if (keys.size === 2 && parts.length === 2 && parts.every((p) => p.e === 1 && (p.name === 'sin' || p.name === 'cos'))) return productToSum(f, parts, d);
    if (keys.size !== 1) return null;
    const A = parts[0].arg;
    const ex = { sin: 0, cos: 0, tan: 0, cot: 0, sec: 0, csc: 0 };
    parts.forEach((p) => { ex[p.name] += p.e; });
    const m = ex.sin + ex.tan - ex.cot - ex.csc;   // as sin^m cos^n
    const n = ex.cos - ex.tan + ex.cot - ex.sec;
    const s = fn('sin', A), c = fn('cos', A);
    const At = T(A);
    const pw = (b, k) => pow(b, num(k));
    const only = (names) => parts.every((p) => names.includes(p.name) && p.e > 0);
    if (only(['tan', 'sec'])) return tanSec(f, A, ex.tan, ex.sec, 'tan', 'sec', d);
    if (only(['cot', 'csc'])) return tanSec(f, A, ex.cot, ex.csc, 'cot', 'csc', d);
    // odd power: peel one factor and use sin² + cos² = 1
    if (m >= 3 && m % 2 === 1) {
      const k = (m - 1) / 2;
      const terms = [];
      for (let j = 0; j <= k; j++) terms.push(mul([num(binom(k, j) * (j % 2 ? -1 : 1)), s, pw(c, 2 * j + n)]));
      return rewriteStep(f, add(terms), 'trigPowers', 'Identity', '\\sin^{' + m + '} ' + At + ' = \\sin ' + At + '\\left(1 - \\cos^{2} ' + At + '\\right)^{' + k + '}', d);
    }
    if (n >= 3 && n % 2 === 1) {
      const k = (n - 1) / 2;
      const terms = [];
      for (let j = 0; j <= k; j++) terms.push(mul([num(binom(k, j) * (j % 2 ? -1 : 1)), c, pw(s, 2 * j + m)]));
      return rewriteStep(f, add(terms), 'trigPowers', 'Identity', '\\cos^{' + n + '} ' + At + ' = \\cos ' + At + '\\left(1 - \\sin^{2} ' + At + '\\right)^{' + k + '}', d);
    }
    // both even and non-negative: half-angle identities
    if (m >= 0 && n >= 0 && m % 2 === 0 && n % 2 === 0 && m + n >= 2) {
      const c2 = fn('cos', mul([TWO, A]));
      const g = expanded(mul([pw(mul([HALF, sub(ONE, c2)]), m / 2), pw(mul([HALF, add([ONE, c2])]), n / 2)]));
      const A2 = T(S(mul([TWO, A])));
      return rewriteStep(f, g, 'halfAngle', 'Identity',
        (m ? '\\sin^{2} ' + At + ' = \\tfrac12\\left(1 - \\cos ' + A2 + '\\right)' : '') + (m && n ? ',\\quad ' : '') +
        (n ? '\\cos^{2} ' + At + ' = \\tfrac12\\left(1 + \\cos ' + A2 + '\\right)' : ''), d);
    }
    // tan/sec family (m even ≥ 0, n < 0) and cot/csc family (n even ≥ 0, m < 0)
    if (m >= 0 && m % 2 === 0 && n < 0 && -n >= m) return tanSec(f, A, m, -n - m, 'tan', 'sec', d);
    if (n >= 0 && n % 2 === 0 && m < 0 && -m >= n) return tanSec(f, A, n, -m - n, 'cot', 'csc', d);
    if (parts.some((p) => p.name !== 'sin' && p.name !== 'cos')) {
      return rewriteStep(f, mul([pw(s, m), pw(c, n)]), 'trigPowers', 'Rewrite', '\\text{in terms of } \\sin ' + At + ' \\text{ and } \\cos ' + At, d);
    }
    return null;
  }
  // ∫ t^a s^b  with (t, s) = (tan, sec) or (cot, csc); 1 + t² = s²
  function tanSec(f, A, a, b, tn, sn, d) {
    const t = fn(tn, A), s = fn(sn, A);
    const At = T(A);
    const pw = (x, k) => pow(x, num(k));
    const L = lin(A);
    if (a === 0) {
      if (b < 3) return null; // table
      // reduction formula
      const kid = I(pw(s, b - 2), d);
      if (!kid) return null;
      const st = mk(f);
      st.rules = ['reduction'];
      st.formula = stmt('reduction');
      const sign = sn === 'sec' ? ONE : NEG1;
      const head = mul([sign, pw(s, b - 2), t, inv(mul([num(b - 1), L.a]))]);
      const k = num(b - 2, b - 1);
      st.setup = tex(add([P(S(head)), mul([k, INT(pw(s, b - 2))])]));
      st.children = [kid];
      return done(st, add([head, mul([k, kid.result])]), tex(add([P(S(head)), mul([k, P(kid.result)])])));
    }
    if (b === 0) {
      if (a < 2) return null;
      const g = add([mul([pw(t, a - 2), pw(s, 2)]), neg(pw(t, a - 2))]);
      return rewriteStep(f, g, 'reduction', 'Identity', '\\' + tn + '^{2} ' + At + ' = \\' + sn + '^{2} ' + At + ' - 1', d);
    }
    if (b % 2 === 0 && b >= 4) {
      const g = expanded(mul([pw(t, a), pw(add([ONE, pw(t, 2)]), (b - 2) / 2), pw(s, 2)]));
      return rewriteStep(f, g, 'trigPowers', 'Identity', '\\' + sn + '^{' + b + '} ' + At + ' = \\left(1 + \\' + tn + '^{2} ' + At + '\\right)^{' + ((b - 2) / 2) + '}\\' + sn + '^{2} ' + At, d);
    }
    if (a % 2 === 1 && a >= 3) {
      const g = expanded(mul([pw(add([pw(s, 2), NEG1]), (a - 1) / 2), pw(s, b), t]));
      return rewriteStep(f, g, 'trigPowers', 'Identity', '\\' + tn + '^{' + (a - 1) + '} ' + At + ' = \\left(\\' + sn + '^{2} ' + At + ' - 1\\right)^{' + ((a - 1) / 2) + '}', d);
    }
    if (b % 2 === 1 && a >= 2 && a % 2 === 0) {
      const g = expanded(mul([pw(add([pw(s, 2), NEG1]), a / 2), pw(s, b)]));
      return rewriteStep(f, g, 'trigPowers', 'Identity', '\\' + tn + '^{2} ' + At + ' = \\' + sn + '^{2} ' + At + ' - 1', d);
    }
    return null;
  }
  function productToSum(f, parts, d) {
    let [p, q] = parts;
    if (p.name === 'cos' && q.name === 'sin') [p, q] = [q, p];
    const A = p.arg, B = q.arg;
    const sum = S(add([A, B])), dif = S(sub(A, B));
    let g, id;
    const At = T(A), Bt = T(B);
    if (p.name === 'sin' && q.name === 'cos') { g = mul([HALF, add([fn('sin', sum), fn('sin', dif)])]); id = '\\sin a\\cos b = \\tfrac12\\left[\\sin(a+b) + \\sin(a-b)\\right]'; }
    else if (p.name === 'sin') { g = mul([HALF, sub(fn('cos', dif), fn('cos', sum))]); id = '\\sin a\\sin b = \\tfrac12\\left[\\cos(a-b) - \\cos(a+b)\\right]'; }
    else { g = mul([HALF, add([fn('cos', dif), fn('cos', sum)])]); id = '\\cos a\\cos b = \\tfrac12\\left[\\cos(a-b) + \\cos(a+b)\\right]'; }
    return rewriteStep(f, expanded(g), 'productToSum', 'Identity', id + ',\\; a = ' + At + ',\\; b = ' + Bt, d);
  }

  /* 10. u-substitution */
  function Dc(n) {
    try { const r = Calc.derive(n, X, 1).result; Calc.setVar(X); return r; } catch (e) { Calc.setVar(X); return null; }
  }
  function candidates(f) {
    const out = new Map();
    const visit = (n, top) => {
      if (isC(n) || isX(n)) return;
      if (!top && n.type !== 'mul') out.set(key(n), n);
      if (n.type === 'pow' && isX(n.base) && isInt(n.exp) && n.exp.n >= 4) {
        for (let j = 2; j < n.exp.n; j++) if (n.exp.n % j === 0) { const g = S(pow(XV(), num(j))); out.set(key(g), g); }
      }
      Calc.children(n).forEach((c) => visit(c, false));
    };
    visit(f, true);
    out.delete(key(f));
    const arr = Array.from(out.values());
    const size = (n) => key(n).length;
    arr.sort((a, b) => (lin(a) ? 1 : 0) - (lin(b) ? 1 : 0) || size(b) - size(a));
    return arr.slice(0, 10);
  }
  // replace g (and powers related to g) by U
  function subst(n, g, U) {
    const kg = key(g);
    const gp = g.type === 'pow' ? g : null;
    const walk = (m) => {
      if (key(m) === kg) return U;
      if (gp) {
        const mb = m.type === 'pow' ? m.base : m, me = m.type === 'pow' ? m.exp : ONE;
        if (key(mb) === key(gp.base) && (m.type === 'pow' || isX(m))) {
          const r = S(div(me, gp.exp));
          if (isInt(r)) return pow(U, r);
        }
      }
      return mapKids(m, walk);
    };
    return walk(n);
  }
  // late = also try back-solving x = e^u for u = ln x (used only after parts has failed)
  // tan, cot, sec, csc → sin and cos (helps a substitution see through tan x = sin x / cos x)
  function sinCos(n) {
    const R = { tan: (a) => div(fn('sin', a), fn('cos', a)), cot: (a) => div(fn('cos', a), fn('sin', a)), sec: (a) => inv(fn('cos', a)), csc: (a) => inv(fn('sin', a)) };
    const walk = (m) => (m.type === 'func' && R[m.name] ? R[m.name](walk(m.arg)) : mapKids(m, walk));
    return walk(n);
  }
  function sUSub(f, d, late) {
    if (d <= 0) return null;
    const W = freshName(f, ['u', 'w', 't', 's']);
    const U = V(W);
    for (const g of candidates(f)) {
      const gp = Dc(g);
      if (!gp || isZero(gp)) continue;
      const q = S(mul([f, inv(gp)]));
      let q2 = S(subst(q, g, U));
      if (contains(q2, X)) { const q3 = S(subst(S(sinCos(q)), g, U)); if (!contains(q3, X)) q2 = q3; }
      if (contains(q2, X)) {
        // back-solve x in terms of u
        const L = lin(g);
        let xu = null;
        if (L) xu = div(sub(U, L.b), L.a);
        else if (late && g.type === 'func' && g.name === 'ln' && isX(g.arg)) xu = pow(C('e'), U);
        if (!xu) continue;
        q2 = S(replaceVar(q2, X, xu));
        if (contains(q2, X)) continue;
      }
      q2 = withVar(W, () => fresh(q2));
      if (key(S(replaceVar(q2, W, XV()))) === key(f)) continue; // just a renaming
      const kid = withVar(W, () => I(q2, d - 1));
      if (!kid) continue;
      const F = fresh(replaceVar(kid.result, W, g));
      if (!verify(f, F)) continue;
      const st = mk(f);
      st.rules = ['uSub'];
      st.formula = stmt('uSub');
      st.where = vt(W) + ' = ' + T(g) + ',\\; d' + vt(W) + ' = ' + (isOne(gp) ? '' : T(gp) + '\\,') + 'd' + vt();
      st.setup = intTex(q2, W);
      st.children = [kid];
      return done(st, F, tex(replaceVar(P(kid.result), W, P(g))));
    }
    return null;
  }

  function sUSubLn(f, d) { return JSON.stringify(f).includes('"ln"') ? sUSub(f, d, true) : null; }

  /* 11. trigonometric substitution */
  function multiAngle(n, Th) {
    const kt = key(Th);
    const walk = (m) => {
      if (m.type === 'func' && (m.name === 'sin' || m.name === 'cos') && m.arg.type === 'mul' && m.arg.factors.length === 2 &&
        isInt(m.arg.factors[0]) && m.arg.factors[0].n >= 2 && m.arg.factors[0].n <= 8 && key(m.arg.factors[1]) === kt) {
        const k = m.arg.factors[0].n;
        const s1 = fn('sin', Th), c1 = fn('cos', Th);
        let sk = s1, ck = c1;
        for (let i = 2; i <= k; i++) {
          const ns = add([mul([sk, c1]), mul([ck, s1])]);
          const nc = sub(mul([ck, c1]), mul([sk, s1]));
          sk = ns; ck = nc;
        }
        return m.name === 'sin' ? sk : ck;
      }
      return mapKids(m, walk);
    };
    return walk(n);
  }
  function sTrigSub(f, d) {
    if (d <= 0) return null;
    const fs = facs(f);
    const qi = fs.findIndex((g) => { const { b, e } = powOf(g); return isNum(e) && !e.f && (e.d === 2 || (e.d === 1 && e.n < -1)) && !!quadPQ(b); });
    if (qi < 0) return null;
    const others = fs.filter((_, i) => i !== qi);
    if (!others.every((g) => { const { b, e } = powOf(g); return isX(b) && isInt(e); })) return null;
    const { b: Q, e } = powOf(fs[qi]);
    const { p, q } = quadPQ(Q);
    const sp = sgn(p), sq_ = sgn(q);
    let kind;
    if (sp > 0 && sq_ < 0) kind = 'sin'; else if (sp > 0 && sq_ > 0) kind = 'tan'; else if (sp < 0 && sq_ > 0) kind = 'sec'; else return null;
    if (e.d === 1 && kind !== 'tan') return null; // (x² − a²)^(−n): partial fractions
    const a2 = S(kind === 'sin' ? div(p, neg(q)) : kind === 'tan' ? div(p, q) : div(neg(p), q));
    const a = sqrtC(a2);
    const c = kind === 'sin' ? S(neg(q)) : q;
    const W = X === 'theta' ? 'phi' : 'theta';
    const Th = V(W);
    const tr = (nm) => fn(nm, Th);
    const xs = mul([a, tr(kind)]);
    const dxs = kind === 'sin' ? mul([a, tr('cos')]) : kind === 'tan' ? mul([a, sq(tr('sec'))]) : mul([a, tr('sec'), tr('tan')]);
    const rad = kind === 'sin' ? tr('cos') : kind === 'tan' ? tr('sec') : tr('tan');
    const Qe = mul([pow(mul([c, a2]), e), pow(rad, num((2 * e.n) / e.d))]);
    const restTh = replaceVar(prod(others), X, xs);
    const g = withVar(W, () => S(mul([restTh, Qe, dxs])));
    const kid = withVar(W, () => I(g, d - 1));
    if (!kid) return null;
    // back-substitute with the reference triangle
    const R = S(pow(S(div(Q, c)), HALF));
    const x = XV();
    let sT, cT, thT;
    if (kind === 'sin') { sT = div(x, a); cT = div(R, a); thT = fn('asin', div(x, a)); }
    else if (kind === 'tan') { sT = div(x, R); cT = div(a, R); thT = fn('atan', div(x, a)); }
    else { sT = div(R, x); cT = div(a, x); thT = fn('asec', div(x, a)); }
    const MAP = { sin: sT, cos: cT, tan: div(sT, cT), cot: div(cT, sT), sec: inv(cT), csc: inv(sT) };
    const kt = key(Th);
    const tri = (m) => {
      if (m.type === 'var' && m.name === W) return thT;
      if (m.type === 'func' && MAP[m.name] && key(m.arg) === kt) return MAP[m.name];
      return mapKids(m, tri);
    };
    const thRes = withVar(W, () => S(multiAngle(kid.result, Th)));
    const F = fresh(tri(thRes));
    if (contains(F, W)) return null;
    const st = mk(f);
    st.rules = ['trigSub'];
    st.formula = stmt('trigSub');
    const tw = vt(W);
    const xsT = tex(P(S(xs)));
    st.where = vt() + ' = ' + xsT + ',\\; d' + vt() + ' = ' + tex(P(S(dxs))) + '\\,d' + tw + (kind === 'sec' ? '\\quad(' + vt() + ' > ' + T(a) + ')' : '');
    const ca2 = S(mul([c, a2]));
    const Qr = replaceVar(Q, X, xs);
    const Qth = withVar(W, () => T(S(Qr)));
    st.note = { label: 'Simplify', tex: T(Q) + ' = ' + Qth + ' = ' + (isOne(ca2) ? '' : tex(P(ca2))) + '\\' + (kind === 'sin' ? 'cos' : kind === 'tan' ? 'sec' : 'tan') + '^{2}' + tw };
    st.setup = intTex(g, W);
    st.children = [kid];
    st.back = tw + ' = ' + T(thT) + ',\\;\\; \\sin ' + tw + ' = ' + T(S(sT)) + ',\\;\\; \\cos ' + tw + ' = ' + T(S(cT));
    if (kind === 'sec') st.posOnly = true;
    return done(st, F);
  }

  /* 12. integration by parts */
  const INV = new Set(['asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch']);
  const TRIGF = new Set(TRIG6.concat(['sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']));
  function rank(fac) {
    const { b, e } = powOf(fac);
    if (b.type === 'func' && (b.name === 'ln' || b.name === 'log') && isInt(e) && e.n > 0) return 5;
    if (b.type === 'func' && INV.has(b.name) && isInt(e) && e.n > 0) return 4;
    if (Calc.isPoly(fac)) return 3;
    if (b.type === 'func' && TRIGF.has(b.name)) return 2;
    if (isC(b) && !isC(e)) return 1;
    return 0;
  }
  function sParts(f, d) {
    if (d <= 0) return null;
    const fs = facs(f);
    const cands = [];
    if (fs.length === 1) { if (rank(f) >= 4) cands.push({ u: f, dv: ONE, r: rank(f) }); }
    else {
      fs.map((fac, i) => ({ fac, i, r: rank(fac) })).filter((o) => o.r >= 2).sort((a, b) => b.r - a.r).slice(0, 2)
        .forEach((o) => {
          const dv = prod(fs.filter((_, j) => j !== o.i));
          // a trig u only makes sense in the cyclic case ∫ e^{ax} sin(bx)
          if (o.r === 2 && !(rank(dv) === 1 && rank(o.fac) === 2 && isInt(powOf(o.fac).e) && powOf(o.fac).e.n === 1)) return;
          cands.push({ u: o.fac, dv, r: o.r });
        });
    }
    for (const cd of cands) {
      const st = partsOnce(f, cd, d);
      if (st) return st;
    }
    return null;
  }
  const kI = (c) => (isOne(c) ? 'I' : tex(mul([P(c), TEX('I')])));
  function partsOnce(f, cd, d) {
    const { u, dv } = cd;
    const Vst = I(dv, d - 1);
    if (!Vst) return null;
    const v = Vst.result;
    const du = Dc(u);
    if (!du) return null;
    const uv = S(mul([u, v]));
    const w = S(mul([v, du]));
    const st = mk(f);
    st.rules = ['byParts'];
    st.formula = stmt('byParts');
    const dpart = (lhs, n) => lhs + ' = ' + (isOne(n) ? '' : T(n) + '\\,') + 'd' + vt();
    st.where = 'u = ' + T(u) + ',\\; ' + dpart('dv', dv) + ',\\; ' + dpart('du', du) + ',\\; v = ' + T(v);
    st.setup = tex(sub(P(uv), INT(w)));
    const ratio = (a) => S(mul([a, inv(f)]));
    // cyclic, after one round: ∫w = k·I
    let k = ratio(w);
    if (isC(k) && !isZero(k) && !isZero(S(add([ONE, k])))) {
      st.rules.push('cyclicParts');
      st.lhsTex = 'I = ' + st.lhsTex;
      st.children = [cap(Vst, 'find v')];
      const den = S(add([ONE, k]));
      st.combinedTex = 'I = ' + T(uv) + (sgn(k) < 0 ? ' + ' + kI(S(neg(k))) : ' - ' + kI(k)) + '\\;\\Rightarrow\\; ' + kI(den) + ' = ' + T(uv);
      return done(st, mul([uv, inv(den)]));
    }
    // cyclic, after two rounds (e^{ax}·sin/cos(bx) type)
    if (cd.r === 2) {
      const wf = facs(w);
      const ti = wf.findIndex((g) => rank(g) === 2);
      if (ti >= 0) {
        const u2 = wf[ti], dv2 = prod(wf.filter((_, j) => j !== ti));
        const V2 = I(dv2, d - 1);
        const du2 = V2 && Dc(u2);
        if (V2 && du2) {
          const uv2 = S(mul([u2, V2.result]));
          const w2 = S(mul([V2.result, du2]));
          k = ratio(w2);
          const den = S(sub(ONE, k));
          if (isC(k) && !isZero(k) && !isZero(den)) {
            st.rules.push('cyclicParts');
            st.lhsTex = 'I = ' + st.lhsTex;
            st.children = [cap(Vst, 'find v'), cap(V2, 'second round: find v')];
            const A = S(sub(uv, uv2));
            st.backLabel = 'Parts again';
            st.back = 'u = ' + T(u2) + ':\\;\\; \\int ' + T(w) + '\\,d' + vt() + ' = ' + T(uv2) + ' - \\int ' + T(w2) + '\\,d' + vt();
            st.combinedTex = 'I = ' + T(A) + (sgn(k) < 0 ? ' - ' + kI(S(neg(k))) : ' + ' + kI(k)) +
              '\\;\\Rightarrow\\; ' + kI(den) + ' = ' + T(A);
            return done(st, mul([A, inv(den)]));
          }
        }
      }
    }
    const J = I(w, d - 1);
    if (!J) return null;
    st.children = [cap(Vst, 'find v'), cap(J, 'remaining integral')];
    return done(st, sub(uv, J.result), tex(sub(P(uv), P(J.result))));
  }

  /* 13. Weierstrass substitution t = tan(x/2) for rational functions of sin x and cos x */
  // n as a single fraction N/D of rational polynomials in X, or null
  function together(n) {
    if (isNum(n)) return n.f ? null : { N: [n], D: [R1] };
    if (isX(n)) return { N: [R0, R1], D: [R1] };
    switch (n.type) {
      case 'add': {
        let acc = { N: [R0], D: [R1] };
        for (const t of n.terms) {
          const r = together(t);
          if (!r) return null;
          acc = { N: padd(pmul(acc.N, r.D), pmul(r.N, acc.D)), D: pmul(acc.D, r.D) };
        }
        return reduceFrac(acc);
      }
      case 'mul': {
        let acc = { N: [R1], D: [R1] };
        for (const f of n.factors) {
          const r = together(f);
          if (!r) return null;
          acc = reduceFrac({ N: pmul(acc.N, r.N), D: pmul(acc.D, r.D) });
        }
        return acc;
      }
      case 'pow': {
        if (!isInt(n.exp) || Math.abs(n.exp.n) > 12) return null;
        const r = together(n.base);
        if (!r) return null;
        const k = Math.abs(n.exp.n);
        const out = { N: ppow(r.N, k), D: ppow(r.D, k) };
        return n.exp.n < 0 ? { N: out.D, D: out.N } : out;
      }
    }
    return null;
  }
  function pgcd(a, b) {
    a = rtrim(a); b = rtrim(b);
    for (let i = 0; i < 40 && !pzero(b); i++) { const r = pdivmod(a, b).r; a = b; b = r; }
    return pscale(a, rinv(a[a.length - 1]));
  }
  function reduceFrac({ N, D }) {
    if (pzero(N)) return { N: [R0], D: [R1] };
    const g = pgcd(N, D);
    if (g.length > 1) { N = pdivmod(N, g).q; D = pdivmod(D, g).q; }
    const lc = D[D.length - 1];
    return { N: pscale(N, rinv(lc)), D: pscale(D, rinv(lc)) };
  }
  function sWeierstrass(f, d) {
    if (d <= 0) return null;
    let ok = true;
    const scan = (n) => {
      if (n.type === 'func') { if (!TRIG6.includes(n.name) || !isX(n.arg)) ok = false; return; }
      if (isX(n)) { ok = false; return; }
      Calc.children(n).forEach(scan);
    };
    scan(f);
    if (!ok) return null;
    const W = freshName(f, ['t', 'u', 'w']);
    const t = V(W), t2 = sq(t), op = add([ONE, t2]), om = sub(ONE, t2);
    const MAP = { sin: div(mul([TWO, t]), op), cos: div(om, op), tan: div(mul([TWO, t]), om), cot: div(om, mul([TWO, t])), sec: div(op, om), csc: div(op, mul([TWO, t])) };
    const walk = (n) => (n.type === 'func' && MAP[n.name] ? MAP[n.name] : mapKids(n, walk));
    const raw = mul([walk(f), TWO, inv(op)]);
    const g = withVar(W, () => {
      const r = together(S(raw));
      return r ? S(mul([polyTree(r.N), inv(polyTree(r.D))])) : null;
    });
    if (!g) return null;
    const kid = withVar(W, () => I(g, d - 1));
    if (!kid) return null;
    const back = fn('tan', mul([HALF, XV()]));
    const st = mk(f);
    st.rules = ['weierstrass'];
    st.formula = stmt('weierstrass');
    st.where = vt(W) + ' = \\tan\\frac{' + vt() + '}{2},\\; \\sin ' + vt() + ' = \\frac{2' + vt(W) + '}{1+' + vt(W) + '^{2}},\\; \\cos ' + vt() + ' = \\frac{1-' + vt(W) + '^{2}}{1+' + vt(W) + '^{2}},\\; d' + vt() + ' = \\frac{2\\,d' + vt(W) + '}{1+' + vt(W) + '^{2}}';
    st.setup = intTex(g, W);
    st.children = [kid];
    return done(st, fresh(replaceVar(kid.result, W, back)), tex(replaceVar(P(kid.result), W, P(S(back)))));
  }

  /* ---------------- non-elementary integrands ---------------- */
  const NONELEM = {
    erf: 'the error function erf (the Gaussian integral)',
    fresnel: 'the Fresnel integrals S and C',
    si: 'the sine integral Si or cosine integral Ci',
    ei: 'the exponential integral Ei',
    li: 'the logarithmic integral li',
    elliptic: 'elliptic integrals',
    xx: '',
  };
  function nonElemOne(r) {
    const fs = facs(r);
    for (const fac of fs) {
      const { b, e } = powOf(fac);
      if (b.type === 'const' && b.name === 'e') { const p = polyC(e); if (p && p.length >= 3) return 'erf'; }
      if (b.type === 'func' && ['sin', 'cos', 'tan', 'sinh', 'cosh'].includes(b.name)) { const p = polyC(b.arg); if (p && p.length >= 3) return 'fresnel'; }
      if (isX(b) && !isC(e)) return 'xx';
      if (b.type === 'func' && b.name === 'ln' && isX(b.arg) && isInt(e) && e.n < 0) return 'li';
      if (isNum(e) && !e.f && e.d === 2) {
        if (b.type === 'func' && ['sin', 'cos'].includes(b.name)) return 'elliptic';
        const p = polyC(b); if (p && p.length >= 4) return 'elliptic';
      }
    }
    if (fs.length === 2) {
      const xi = fs.findIndex((g) => { const { b, e } = powOf(g); return isX(b) && isInt(e) && e.n < 0; });
      if (xi >= 0) {
        const o = fs[1 - xi];
        const { b, e } = powOf(o);
        if (b.type === 'func' && ['sin', 'cos', 'sinh', 'cosh'].includes(b.name) && lin(b.arg)) return 'si';
        if (isC(b) && lin(e)) return 'ei';
      }
    }
    return null;
  }
  function nonElem(f) {
    for (const t of f.type === 'add' ? f.terms : [f]) {
      const r = prod(facs(t).filter((g) => !isC(g)));
      const m = nonElemOne(r);
      if (m) return m;
    }
    return null;
  }

  /* ---------------- entry point ---------------- */
  function rulesUsed(step, out) {
    out = out || [];
    step.rules.forEach((r) => { if (!out.includes(r)) out.push(r); });
    step.children.forEach((c) => rulesUsed(c, out));
    return out;
  }
  function integrate(tree, v) {
    v = v || 'x';
    memo = new Map(); busy = new Set(); calls = 0; deadline = Date.now() + TIME_LIMIT;
    return withVar(v, () => {
      const f = S(tree);
      CENV = constEnv(f);
      const st = I(f, MAXD);
      if (!st) {
        const ne = nonElem(f);
        const err = new IntegrationError(ne
          ? 'This integral has no elementary antiderivative' + (ne === 'xx' ? '.' : ': it is written with ' + NONELEM[ne] + '.')
          : 'None of the techniques here (table, substitution, parts, partial fractions, trig methods) found an antiderivative.');
        err.nonElementary = !!ne;
        err.special = ne;
        throw err;
      }
      let check = null;
      try { check = { tex: Calc.derive(P(st.result), v, 1).resultTex }; } catch (e) { check = null; }
      Calc.setVar(v);
      return { steps: [st], result: st.result, resultTex: st.resultTex, rules: rulesUsed(st), check, posOnly: !!st.posOnly };
    });
  }

  Object.assign(Calc, { integrate, IntegrationError });
})(typeof window !== 'undefined' ? window : globalThis);
