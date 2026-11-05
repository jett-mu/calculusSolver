/* simplify.js — canonical algebraic simplifier + presentation pass.
 *
 * Canonical form (internal): num, const, var, func, pow, mul (sorted, ≤1 leading number), add (sorted).
 * There is no div/neg in canonical form: a/b → a·b^(-1), -a → (-1)·a.
 * present() converts back to a readable display tree (fractions, minus signs, radicals).
 * Shared by the differentiator now and the integrator later. */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const { num, C, add, mul, div, pow, neg, fn, radd, rmul, rneg, rval, rpowInt,
    isNum, isZero, isOne, isInt, isNeg, numEq, key, isConstant } = Calc;

  let MAIN = 'x';
  const setVar = (v) => { MAIN = v; };
  const getVar = () => MAIN;

  const ONE = num(1), ZERO = num(0), NEG1 = num(-1), TWO = num(2);
  const canon = (n) => { n.c = true; return n; };

  function S(n) {
    if (n.c) return n;
    switch (n.type) {
      case 'num': case 'const': case 'var': return n;
      case 'neg': return sMul([NEG1, S(n.arg)]);
      case 'div': return sMul([S(n.num), sPow(S(n.den), NEG1)]);
      case 'add': return sAdd(n.terms.map(S));
      case 'mul': return sMul(n.factors.map(S));
      case 'pow': return sPow(S(n.base), S(n.exp));
      case 'func': return sFunc(n.name, S(n.arg), n.base ? S(n.base) : null);
    }
    throw new Error('Unknown node ' + n.type);
  }

  /* ---------------- functions ---------------- */
  const ODD = new Set(['sin', 'tan', 'cot', 'csc', 'asin', 'atan', 'acsc', 'sinh', 'tanh', 'coth', 'csch', 'asinh', 'atanh', 'acoth', 'acsch']);
  const EVEN = new Set(['cos', 'sec', 'cosh', 'sech', 'abs']);
  const AT_ZERO = { sin: 0, cos: 1, tan: 0, sec: 1, sinh: 0, cosh: 1, tanh: 0, sech: 1, asin: 0, atan: 0, asinh: 0, atanh: 0, abs: 0 };

  // If `a` has a negative leading coefficient, return -a; else null.
  function negated(a) {
    if (isNum(a) && isNeg(a)) return rneg(a);
    if (a.type === 'mul' && isNeg(a.factors[0])) return sMul([NEG1, a]);
    return null;
  }
  function isPositive(n) {
    if (isNum(n)) return n.n > 0;
    if (n.type === 'const') return true;
    if (n.type === 'pow') {
      if (isPositive(n.base)) return true;
      if (isInt(n.exp) && n.exp.n % 2 === 0) return false; // nonnegative but may be 0
    }
    if (n.type === 'func' && (n.name === 'cosh' || n.name === 'sech' || n.name === 'exp')) return true;
    return false;
  }
  function sFunc(name, a, b) {
    if (name === 'sqrt') return sPow(a, num(1, 2));
    if (name === 'cbrt') return sPow(a, num(1, 3));
    if (name === 'exp') return sPow(C('e'), a);
    if (name === 'log') {
      if (!b) b = num(10);
      if (b.type === 'const' && b.name === 'e') return sFunc('ln', a);
      if (key(a) === key(b)) return ONE;
      if (isOne(a)) return ZERO;
      return canon(fn('log', a, b));
    }
    if (name === 'ln') {
      if (isOne(a)) return ZERO;
      if (a.type === 'const' && a.name === 'e') return ONE;
      if (a.type === 'pow' && a.base.type === 'const' && a.base.name === 'e') return a.exp;
      return canon(fn('ln', a));
    }
    const m = negated(a);
    if (m && ODD.has(name)) return sMul([NEG1, sFunc(name, m)]);
    if (m && EVEN.has(name)) return sFunc(name, m);
    if (isZero(a) && name in AT_ZERO) return num(AT_ZERO[name]);
    if (name === 'abs') {
      if (isNum(a)) return a.f ? { type: 'num', n: Math.abs(a.n), d: 1, f: true } : num(Math.abs(a.n), a.d);
      if (isPositive(a)) return a;
      if (a.type === 'func' && a.name === 'abs') return a;
      if (a.type === 'pow' && isInt(a.exp) && a.exp.n % 2 === 0) return a;
    }
    return canon(fn(name, a));
  }

  /* ---------------- powers ---------------- */
  function intRoot(m, q) {
    if (m < 0) return null;
    const r = Math.round(Math.pow(m, 1 / q));
    for (const c of [r - 1, r, r + 1]) if (c >= 0 && Math.pow(c, q) === m) return c;
    return null;
  }
  function exactRoot(b, e) {
    // b^(p/q) with exact rational result, or null
    if (b.f || e.f) return null;
    const q = e.d;
    let sign = 1, n = b.n;
    if (n < 0) { if (q % 2 === 0) return null; sign = -1; n = -n; }
    const rn = intRoot(n, q), rd = intRoot(b.d, q);
    if (rn === null || rd === null) return null;
    return rpowInt(num(sign * rn, rd), e.n);
  }
  function sPow(b, e) {
    if (isZero(e)) return ONE;
    if (isOne(e)) return b;
    if (isOne(b)) return ONE;
    if (isZero(b) && isNum(e) && e.n > 0) return ZERO;
    if (isNum(b) && isNum(e)) {
      if (isInt(e) && Math.abs(e.n) <= 512 && !(isZero(b) && e.n < 0)) return rpowInt(b, e.n);
      if ((b.f || e.f) && b.n > 0) return { type: 'num', n: Math.pow(rval(b), rval(e)), d: 1, f: true };
      const r = exactRoot(b, e);
      if (r) return r;
    }
    if (b.type === 'pow') {
      const inner = b.exp;
      if (isInt(e)) return sPow(b.base, sMul([inner, e]));
      if (isNum(inner) && isNum(e) && !inner.f && !e.f) {
        const prod = rmul(inner, e);
        // (u^2)^(1/2) = |u|  — even power under an even root
        if (inner.n % 2 === 0 && !prod.f && prod.n % 2 !== 0 && !isPositive(b.base)) return sPow(sFunc('abs', b.base), prod);
        return sPow(b.base, prod);
      }
      if (isPositive(b.base)) return sPow(b.base, sMul([inner, e]));
    }
    if (b.type === 'mul' && isInt(e)) return sMul(b.factors.map((f) => sPow(f, e)));
    if (b.type === 'func' && b.name === 'abs' && isInt(e) && e.n % 2 === 0) return sPow(b.arg, e);
    if (b.type === 'const' && b.name === 'e' && e.type === 'func' && e.name === 'ln') return e.arg;
    return canon(pow(b, e));
  }

  /* ---------------- products ---------------- */
  function frank(f) {
    if (isNum(f)) return 0;
    if (isConstant(f, MAIN)) {
      const b = f.type === 'pow' ? f.base : f;
      return b.type === 'func' || b.type === 'add' ? 5 : 1;
    }
    const b = f.type === 'pow' ? f.base : f;
    if (b.type === 'var') return 2;
    if (f.type === 'pow' && isConstant(f.base, MAIN)) return 3; // exponentials a^u
    if (b.type === 'func') return 4;
    if (b.type === 'add') return 6;
    return 7;
  }
  const cmp = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
  const factorOrder = (a, b) => frank(a) - frank(b) || cmp(key(a), key(b));

  function sMul(fs) {
    const flat = [];
    for (const f of fs) { if (f.type === 'mul') flat.push(...f.factors); else flat.push(f); }
    let coef = ONE;
    const groups = new Map();
    for (const f of flat) {
      if (isNum(f)) { coef = rmul(coef, f); continue; }
      let b = f, e = ONE;
      if (f.type === 'pow') { b = f.base; e = f.exp; }
      const k = key(b);
      const g = groups.get(k);
      if (g) { g.exps.push(e); g.orig = null; }
      else groups.set(k, { base: b, exps: [e], orig: f });
    }
    if (isZero(coef)) return ZERO;
    let out = [];
    let again = false;
    for (const g of groups.values()) {
      const p = g.orig ? g.orig : sPow(g.base, sAdd(g.exps));
      if (isNum(p)) { coef = rmul(coef, p); continue; }
      if (p.type === 'mul') again = true;
      out.push(p);
    }
    if (isZero(coef)) return ZERO;
    if (again) return sMul([coef].concat(out));
    const cl = clearNested(out);
    if (cl) return sMul([coef].concat(cl));
    const c = tryCancel(out);
    if (c) return sMul([coef].concat(c));
    out.sort(factorOrder);
    if (!out.length) return coef;
    if (isOne(coef) && out.length === 1) return out[0];
    return canon(mul(isOne(coef) ? out : [coef].concat(out)));
  }

  // x^-2 · (1 + x^-2)^-1  →  (x^2 + 1)^-1   (clear fractions nested inside a denominator)
  const negPowCount = (A) => A.terms.reduce((s, t) => s + (t.type === 'mul' ? t.factors : [t])
    .filter((f) => f.type === 'pow' && isNum(f.exp) && f.exp.n < 0).length, 0);
  function clearNested(out) {
    for (let i = 0; i < out.length; i++) {
      const f = out[i];
      if (!(f.type === 'pow' && f.base.type === 'add' && isInt(f.exp) && f.exp.n < 0)) continue;
      const A = f.base, before = negPowCount(A);
      if (!before) continue;
      for (let j = 0; j < out.length; j++) {
        const g = out[j];
        if (j === i || !(g.type === 'pow' && g.base.type !== 'add' && isNum(g.exp) && g.exp.n < 0)) continue;
        const m = rmul(g.exp, Calc.rinv(f.exp)); // spread b^(-m) over A^(-k): multiply A by b^(m/k)
        const A2 = sAdd(A.terms.map((t) => sMul([t, sPow(g.base, m)])));
        if (A2.type === 'add' && negPowCount(A2) < before) {
          const res = out.filter((_, k) => k !== i && k !== j);
          res.push(canon(pow(A2, f.exp)));
          return res;
        }
      }
    }
    return null;
  }

  // Factor common monomials out of a sum: a·x^2 + b·x^3 → x^2 (a + b·x)
  function termFactorMap(t) {
    const m = new Map();
    const fs = t.type === 'mul' ? t.factors : [t];
    for (const f of fs) {
      if (isNum(f)) continue;
      const b = f.type === 'pow' ? f.base : f;
      const e = f.type === 'pow' ? f.exp : ONE;
      m.set(key(b), { base: b, exp: e });
    }
    return m;
  }
  function factorCommon(A) {
    const maps = A.terms.map(termFactorMap);
    const common = [];
    for (const [k, g] of maps[0]) {
      if (!isNum(g.exp) || g.exp.n <= 0) continue;
      let minE = g.exp, ok = true;
      for (let i = 1; i < maps.length; i++) {
        const h = maps[i].get(k);
        if (!h || !isNum(h.exp) || h.exp.n <= 0) { ok = false; break; }
        if (rval(h.exp) < rval(minE)) minE = h.exp;
      }
      if (ok) common.push({ base: g.base, exp: minE });
    }
    if (!common.length) return null;
    const divisor = common.map((c) => sPow(c.base, rneg(c.exp)));
    const rest = sAdd(A.terms.map((t) => sMul([t].concat(divisor))));
    return { common: common.map((c) => sPow(c.base, c.exp)), rest };
  }
  // Cancel a sum against a matching denominator: (sec x tan x + sec²x)/(sec x + tan x) → sec x
  function tryCancel(out) {
    const dens = [];
    const denKeys = new Set();
    out.forEach((f, i) => {
      if (f.type === 'pow' && isNum(f.exp) && f.exp.n < 0) {
        if (f.base.type === 'add') dens.push(i);
        denKeys.add(key(f.base));
      }
    });
    if (!denKeys.size) return null;
    for (let i = 0; i < out.length; i++) {
      const A = out[i];
      if (A.type !== 'add') continue;
      const fc = factorCommon(A);
      if (!fc) continue;
      // (x²cos x − 2x sin x)·x⁻⁴ → x(x cos x − 2 sin x)·x⁻⁴ → (x cos x − 2 sin x)·x⁻³
      if (fc.common.some((c) => denKeys.has(key(c.type === 'pow' ? c.base : c)))) {
        const res = out.slice();
        res[i] = mul(fc.common.concat([fc.rest]));
        return res;
      }
      if (fc.rest.type !== 'add') continue;
      const rk = key(fc.rest);
      const negRest = sMul([NEG1, fc.rest]);
      const nk = key(negRest);
      for (const j of dens) {
        const bk = key(out[j].base);
        if (bk === rk || bk === nk) {
          const res = out.slice();
          res[i] = mul(fc.common.concat(bk === rk ? [fc.rest] : [NEG1, negRest]));
          return res;
        }
      }
    }
    return null;
  }

  /* ---------------- sums ---------------- */
  function isPoly(n) {
    if (isConstant(n, MAIN)) return true;
    switch (n.type) {
      case 'var': return true;
      case 'add': return n.terms.every(isPoly);
      case 'mul': return n.factors.every(isPoly);
      case 'pow': return isInt(n.exp) && n.exp.n >= 0 && isPoly(n.base);
    }
    return false;
  }
  const sumPow = (f) => f.type === 'pow' && f.base.type === 'add' && isInt(f.exp) && f.exp.n >= 2 && f.exp.n <= 4;
  function expand(t) {
    let acc = [[]];
    const fs = t.type === 'mul' ? t.factors : [t];
    for (const f of fs) {
      let opts;
      if (f.type === 'add') opts = [f.terms];
      else if (sumPow(f)) opts = Array(f.exp.n).fill(f.base.terms);
      else opts = [[f]];
      for (const terms of opts) {
        const nacc = [];
        for (const a of acc) for (const u of terms) nacc.push(a.concat([u]));
        acc = nacc;
        if (acc.length > 64) return null;
      }
    }
    return acc.map((x) => sMul(x));
  }
  function degree(t) {
    if (isNum(t)) return -1;
    const fs = t.type === 'mul' ? t.factors : [t];
    let d = 0, other = false;
    for (const f of fs) {
      if (isConstant(f, MAIN)) continue;
      if (f.type === 'var') d += 1;
      else if (f.type === 'pow' && f.base.type === 'var' && isNum(f.exp)) d += rval(f.exp);
      else other = true;
    }
    return d + (other ? 0.5 : 0);
  }
  const stripCoef = (t) => (t.type === 'mul' && isNum(t.factors[0]) ? mul(t.factors.slice(1)) : t);
  const termOrder = (a, b) => degree(b) - degree(a) || cmp(key(stripCoef(a)), key(stripCoef(b)));

  // a² + s·b² = 1 identities
  const PYTH = [['sin', 'cos', 1], ['cosh', 'sinh', -1], ['sec', 'tan', -1], ['csc', 'cot', -1]];
  function pythagorean(groups) {
    let gained = ZERO;
    for (const g of Array.from(groups.values())) {
      const r = g.rest;
      if (!(r.type === 'pow' && numEq(r.exp, 2) && r.base.type === 'func')) continue;
      for (const [a, b, s] of PYTH) {
        if (r.base.name !== a) continue;
        const ka = key(r), kb = '^(' + b + '(' + key(r.base.arg) + '),#2)';
        const ga = groups.get(ka), gb = groups.get(kb);
        if (!ga || !gb) continue;
        // c·(a² + s·b²) = c  when the coefficients line up
        if (key(gb.c) === key(s === 1 ? ga.c : rneg(ga.c))) {
          gained = radd(gained, ga.c);
          groups.delete(ka); groups.delete(kb);
        }
      }
    }
    return gained;
  }

  function sAdd(ts) {
    const flat = [];
    const pushTerm = (t) => {
      if (t.type === 'add') { t.terms.forEach(pushTerm); return; }
      if (t.type === 'mul') {
        if (t.factors.length === 2 && isNum(t.factors[0]) && t.factors[1].type === 'add') {
          t.factors[1].terms.forEach((u) => pushTerm(sMul([t.factors[0], u])));
          return;
        }
        if (t.factors.some((f) => f.type === 'add' || sumPow(f)) && isPoly(t)) {
          const ex = expand(t);
          if (ex) { ex.forEach(pushTerm); return; }
        }
      }
      if (sumPow(t) && isPoly(t)) {
        const ex = expand(t);
        if (ex) { ex.forEach(pushTerm); return; }
      }
      flat.push(t);
    };
    ts.forEach(pushTerm);
    const groups = new Map();
    let constant = ZERO;
    for (const t of flat) {
      if (isNum(t)) { constant = radd(constant, t); continue; }
      let c = ONE, rest = t;
      if (t.type === 'mul' && isNum(t.factors[0])) {
        c = t.factors[0];
        const r = t.factors.slice(1);
        rest = r.length === 1 ? r[0] : canon(mul(r));
      }
      const k = key(rest);
      const g = groups.get(k);
      if (g) g.c = radd(g.c, c); else groups.set(k, { c, rest });
    }
    constant = radd(constant, pythagorean(groups));
    const out = [];
    for (const g of groups.values()) {
      if (isZero(g.c)) continue;
      if (isOne(g.c)) out.push(g.rest);
      else out.push(canon(mul([g.c].concat(g.rest.type === 'mul' ? g.rest.factors : [g.rest]))));
    }
    if (!isZero(constant)) out.push(constant);
    if (!out.length) return ZERO;
    if (out.length === 1) return out[0];
    out.sort(termOrder);
    return canon(add(out));
  }

  /* ---------------- presentation ---------------- */
  function startsNegDisplay(n) {
    if (n.type === 'neg') return true;
    if (n.type === 'num') return n.n < 0;
    return false;
  }
  function P(n) {
    switch (n.type) {
      case 'num': case 'const': case 'var': return n;
      case 'add': {
        const ts = n.terms.map(P);
        if (ts.length > 1 && startsNegDisplay(ts[0])) {
          const i = ts.findIndex((t) => !startsNegDisplay(t));
          if (i > 0) { const [t] = ts.splice(i, 1); ts.unshift(t); }
        }
        return add(ts);
      }
      case 'mul': return presentMul(n.factors);
      case 'pow': {
        const e = n.exp;
        if (isNum(e) && isNeg(e)) return div(ONE, P(sPow(n.base, rneg(e))));
        if (numEq(e, 1, 2)) return fn('sqrt', P(n.base));
        if (numEq(e, 1, 3)) return fn('cbrt', P(n.base));
        if (numEq(e, 2, 3)) return fn('cbrt', pow(P(n.base), TWO));
        return pow(P(n.base), P(e));
      }
      case 'func': return fn(n.name, P(n.arg), n.base);
      default: return n; // already a display node
    }
  }
  function presentMul(factors) {
    let c = ONE;
    const numer = [], denom = [];
    for (const f of factors) {
      if (isNum(f)) { c = rmul(c, f); continue; }
      if (f.type === 'pow' && isNum(f.exp) && isNeg(f.exp)) { denom.push(P(sPow(f.base, rneg(f.exp)))); continue; }
      numer.push(P(f));
    }
    const negSign = isNeg(c);
    const a = negSign ? rneg(c) : c;
    const p = a.f ? a : num(a.n), q = a.f ? ONE : num(a.d);
    let top = [];
    if (!isOne(p) || numer.length === 0) top.push(p);
    top = top.concat(numer);
    const topN = top.length === 1 ? top[0] : mul(top);
    const bot = (isOne(q) ? [] : [q]).concat(denom);
    const r = bot.length ? div(topN, bot.length === 1 ? bot[0] : mul(bot)) : topN;
    return negSign ? neg(r) : r;
  }

  const simplify = (n) => S(n);
  const present = (n) => P(S(n));
  const texOf = (n) => Calc.tex(present(n));

  Object.assign(Calc, { simplify, present, texOf, setVar, getVar, isPoly, factorCommon, ONE, ZERO, NEG1, TWO });
})(typeof window !== 'undefined' ? window : globalThis);
