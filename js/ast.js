/* ast.js — expression nodes, exact rational numbers, evaluation, keys, LaTeX printing.
 * Plain script: attaches to the global `Calc` namespace (works from file:// and in Node). */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});

  /* ---------------- Rational numbers ----------------
   * A number node is { type:'num', n, d } with d > 0 and gcd(n,d)=1.
   * If exact arithmetic would overflow, we fall back to a float: { n: value, d: 1, f: true }. */
  function gcd(a, b) {
    a = Math.abs(a); b = Math.abs(b);
    while (b) { const t = a % b; a = b; b = t; }
    return a;
  }
  function num(n, d) {
    if (d === undefined) d = 1;
    if (!Number.isInteger(n) || !Number.isInteger(d) || d === 0) {
      return { type: 'num', n: n / d, d: 1, f: true };
    }
    if (d < 0) { n = -n; d = -d; }
    const g = gcd(n, d) || 1;
    n /= g; d /= g;
    if (!Number.isSafeInteger(n) || !Number.isSafeInteger(d)) return { type: 'num', n: n / d, d: 1, f: true };
    if (n === 0) n = 0; // normalise -0
    return { type: 'num', n, d };
  }
  const isFloat = (a) => !!a.f;
  const rval = (a) => a.n / a.d;
  function radd(a, b) {
    if (a.f || b.f) return { type: 'num', n: rval(a) + rval(b), d: 1, f: true };
    return num(a.n * b.d + b.n * a.d, a.d * b.d);
  }
  function rmul(a, b) {
    if (a.f || b.f) return { type: 'num', n: rval(a) * rval(b), d: 1, f: true };
    return num(a.n * b.n, a.d * b.d);
  }
  function rneg(a) { return a.f ? { type: 'num', n: -a.n, d: 1, f: true } : num(-a.n, a.d); }
  function rinv(a) { return a.f ? { type: 'num', n: 1 / a.n, d: 1, f: true } : num(a.d, a.n); }
  function rpowInt(a, k) {
    if (k < 0) return rpowInt(rinv(a), -k);
    if (a.f) return { type: 'num', n: Math.pow(a.n, k), d: 1, f: true };
    let n = 1, d = 1;
    for (let i = 0; i < k; i++) { n *= a.n; d *= a.d; if (!Number.isSafeInteger(n) || !Number.isSafeInteger(d)) return { type: 'num', n: Math.pow(rval(a), k), d: 1, f: true }; }
    return num(n, d);
  }
  const isNum = (x) => x && x.type === 'num';
  const isZero = (x) => isNum(x) && x.n === 0;
  const isOne = (x) => isNum(x) && x.n === 1 && x.d === 1;
  const isInt = (x) => isNum(x) && !x.f && x.d === 1;
  const isNeg = (x) => isNum(x) && x.n < 0;
  const numEq = (x, n, d) => isNum(x) && !x.f && x.n === n && x.d === (d || 1);

  /* ---------------- Node constructors ---------------- */
  const C = (name) => ({ type: 'const', name });           // 'pi' | 'e'
  const V = (name) => ({ type: 'var', name });
  const add = (terms) => ({ type: 'add', terms });
  const mul = (factors) => ({ type: 'mul', factors });
  const div = (a, b) => ({ type: 'div', num: a, den: b });
  const pow = (b, e) => ({ type: 'pow', base: b, exp: e });
  const neg = (a) => ({ type: 'neg', arg: a });
  const mulDot = (factors) => ({ type: 'mul', factors, dot: true }); // printed with explicit \cdot
  const TEX = (s) => ({ type: 'tex', s });                             // literal LaTeX placeholder
  const fn = (name, arg, base) => (base ? { type: 'func', name, arg, base } : { type: 'func', name, arg });

  /* ---------------- Structural helpers ---------------- */
  function children(n) {
    switch (n.type) {
      case 'add': return n.terms;
      case 'mul': return n.factors;
      case 'div': return [n.num, n.den];
      case 'pow': return [n.base, n.exp];
      case 'neg': return [n.arg];
      case 'func': return n.base ? [n.arg, n.base] : [n.arg];
      default: return [];
    }
  }
  function contains(n, v) {
    if (n.type === 'var') return n.name === v;
    return children(n).some((c) => contains(c, v));
  }
  const isConstant = (n, v) => !contains(n, v);
  function freeVars(n, out) {
    out = out || new Set();
    if (n.type === 'var') out.add(n.name);
    children(n).forEach((c) => freeVars(c, out));
    return out;
  }

  /* Canonical key (used for like-term collection and equality). */
  function key(n) {
    switch (n.type) {
      case 'num': return n.f ? '#' + n.n : '#' + n.n + (n.d !== 1 ? '/' + n.d : '');
      case 'const': return '@' + n.name;
      case 'var': return '$' + n.name;
      case 'add': return '+(' + n.terms.map(key).join(',') + ')';
      case 'mul': return '*(' + n.factors.map(key).join(',') + ')';
      case 'div': return '/(' + key(n.num) + ',' + key(n.den) + ')';
      case 'pow': return '^(' + key(n.base) + ',' + key(n.exp) + ')';
      case 'neg': return '~(' + key(n.arg) + ')';
      case 'func': return n.name + (n.base ? '_' + key(n.base) : '') + '(' + key(n.arg) + ')';
    }
    return '?';
  }

  /* ---------------- Numeric evaluation ---------------- */
  const FN_EVAL = {
    sin: Math.sin, cos: Math.cos, tan: Math.tan,
    cot: (u) => 1 / Math.tan(u), sec: (u) => 1 / Math.cos(u), csc: (u) => 1 / Math.sin(u),
    asin: Math.asin, acos: Math.acos, atan: Math.atan,
    acot: (u) => Math.PI / 2 - Math.atan(u), asec: (u) => Math.acos(1 / u), acsc: (u) => Math.asin(1 / u),
    sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
    coth: (u) => 1 / Math.tanh(u), sech: (u) => 1 / Math.cosh(u), csch: (u) => 1 / Math.sinh(u),
    asinh: Math.asinh, acosh: Math.acosh, atanh: Math.atanh,
    acoth: (u) => Math.atanh(1 / u), asech: (u) => Math.acosh(1 / u), acsch: (u) => Math.asinh(1 / u),
    ln: Math.log, exp: Math.exp, sqrt: Math.sqrt, cbrt: Math.cbrt, abs: Math.abs,
  };
  function realPow(b, e, expNode) {
    if (b < 0 && expNode && isNum(expNode) && !expNode.f && expNode.d % 2 === 1) {
      // odd-denominator rational power of a negative number is real
      const r = Math.pow(-b, e);
      return expNode.n % 2 === 0 ? r : -r;
    }
    return Math.pow(b, e);
  }
  function evaluate(n, env) {
    switch (n.type) {
      case 'num': return n.n / n.d;
      case 'const': return n.name === 'pi' ? Math.PI : Math.E;
      case 'var': return env && n.name in env ? env[n.name] : NaN;
      case 'add': return n.terms.reduce((s, t) => s + evaluate(t, env), 0);
      case 'mul': return n.factors.reduce((s, t) => s * evaluate(t, env), 1);
      case 'div': return evaluate(n.num, env) / evaluate(n.den, env);
      case 'neg': return -evaluate(n.arg, env);
      case 'pow': return realPow(evaluate(n.base, env), evaluate(n.exp, env), n.exp);
      case 'func': {
        const u = evaluate(n.arg, env);
        if (n.name === 'log') return Math.log(u) / Math.log(n.base ? evaluate(n.base, env) : 10);
        const f = FN_EVAL[n.name];
        return f ? f(u) : NaN;
      }
    }
    return NaN;
  }

  /* ---------------- LaTeX printing ----------------
   * Prints a *display* tree (num/const/var/add/mul/div/pow/neg/func).
   * Canonical trees from the simplifier are first converted with Calc.present(). */
  const FN_TEX = {
    sin: '\\sin', cos: '\\cos', tan: '\\tan', cot: '\\cot', sec: '\\sec', csc: '\\csc',
    asin: '\\arcsin', acos: '\\arccos', atan: '\\arctan',
    acot: '\\operatorname{arccot}', asec: '\\operatorname{arcsec}', acsc: '\\operatorname{arccsc}',
    sinh: '\\sinh', cosh: '\\cosh', tanh: '\\tanh', coth: '\\coth',
    sech: '\\operatorname{sech}', csch: '\\operatorname{csch}',
    asinh: '\\operatorname{arsinh}', acosh: '\\operatorname{arcosh}', atanh: '\\operatorname{artanh}',
    acoth: '\\operatorname{arcoth}', asech: '\\operatorname{arsech}', acsch: '\\operatorname{arcsch}',
    ln: '\\ln',
  };
  const GREEK = { theta: '\\theta', alpha: '\\alpha', beta: '\\beta', phi: '\\varphi', omega: '\\omega' };

  // 6 significant digits; very large or small values in scientific notation, split into mantissa and power of ten
  // (JavaScript's own "1.234e+291" would read as 1.234·e + 291)
  function floatParts(v) {
    const s = String(Number(v.toPrecision(6)));
    const m = s.match(/^(-?[\d.]+)e([+-]\d+)$/);
    return m ? { mant: m[1], exp: parseInt(m[2], 10) } : { plain: s };
  }
  function fmtFloat(v) {
    if (!isFinite(v)) return v > 0 ? '\\infty' : v < 0 ? '-\\infty' : '\\text{NaN}';
    const p = floatParts(v);
    if (p.plain) return p.plain;
    const pow10 = '10^{' + p.exp + '}';
    if (p.mant === '1') return pow10;
    if (p.mant === '-1') return '-' + pow10;
    return p.mant + ' \\times ' + pow10;
  }
  // plain-text form the parser reads back: 1.234*10^291, 5*10^(-7)
  function strFloat(v) {
    if (!isFinite(v)) return v > 0 ? 'Infinity' : v < 0 ? '-Infinity' : 'NaN';
    const p = floatParts(v);
    if (p.plain) return p.plain;
    return p.mant + '*10^' + (p.exp < 0 ? '(' + p.exp + ')' : p.exp);
  }
  function numTex(n) {
    if (n.f) return fmtFloat(n.n);
    const s = n.n < 0 ? '-' : '';
    const a = Math.abs(n.n);
    return n.d === 1 ? s + a : s + '\\frac{' + a + '}{' + n.d + '}';
  }
  const paren = (s) => '\\left(' + s + '\\right)';

  // Does the printed form of this node start with a minus sign?
  function startsNeg(n) {
    if (n.type === 'neg') return true;
    if (n.type === 'num') return n.n < 0;
    if (n.type === 'mul') return n.factors.length > 0 && startsNeg(n.factors[0]);
    if (n.type === 'div') return startsNeg(n.num);
    if (n.type === 'add') return n.terms.length > 0 && startsNeg(n.terms[0]);
    return false;
  }
  // Is the argument simple enough to print without parentheses, e.g. \sin x ?
  function bareArg(a) {
    return a.type === 'var' || a.type === 'const' || (a.type === 'num' && !a.f && a.n >= 0 && a.d === 1);
  }
  function funcHead(n, o) {
    if (n.name === 'log') {
      const b = n.base ? tex(n.base, o) : '10';
      return '\\log_{' + b + '}';
    }
    return FN_TEX[n.name] || '\\operatorname{' + n.name + '}';
  }
  function funcArgTex(n, o) {
    if (n.arg.type === 'func' && n.arg.name === 'abs') return tex(n.arg, o); // \ln\left|x\right|
    return bareArg(n.arg) ? ' ' + tex(n.arg, o) : paren(tex(n.arg, o));
  }

  function tex(n, o) {
    o = o || {};
    switch (n.type) {
      case 'tex': return n.s;
      case 'num': return numTex(n);
      case 'const': return n.name === 'pi' ? '\\pi' : 'e';
      case 'var': return GREEK[n.name] || n.name;
      case 'add': {
        let s = '';
        n.terms.forEach((t, i) => {
          let body = t, minus = false;
          if (t.type === 'neg') { minus = true; body = t.arg; }
          else if (t.type === 'num' && t.n < 0) { minus = true; body = rneg(t); }
          else if (t.type === 'mul' && t.factors.length && isNeg(t.factors[0])) {
            minus = true;
            const c = rneg(t.factors[0]);
            const rest = t.factors.slice(1);
            body = isOne(c) ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([c].concat(rest));
          }
          let b = tex(body, o);
          if (body.type === 'add' || (minus && startsNeg(body))) b = paren(b);
          if (i === 0) s += (minus ? '-' : '') + b;
          else s += (minus ? ' - ' : ' + ') + b;
        });
        return s;
      }
      case 'neg': {
        const a = n.arg;
        const b = tex(a, o);
        return '-' + (a.type === 'add' || startsNeg(a) ? paren(b) : b);
      }
      case 'mul': {
        let s = '';
        let prev = null;
        n.factors.forEach((f, i) => {
          if (i === 0 && numEq(f, -1, 1) && n.factors.length > 1) { s += '-'; return; }
          let b = tex(f, o);
          const needParen = f.type === 'add' || f.type === 'neg' || (i > 0 && startsNeg(f)) ||
            (f.type === 'num' && (f.d !== 1) && n.factors.length > 1 && i > 0);
          if (needParen) b = paren(b);
          if (prev) {
            s += n.dot || needsCdot(prev, f, b) ? ' \\cdot ' : '';
          }
          s += b;
          prev = f;
        });
        return s;
      }
      case 'div': return '\\frac{' + tex(n.num, o) + '}{' + tex(n.den, o) + '}';
      case 'pow': {
        const b = n.base, e = n.exp;
        const et = tex(e, o);
        // \sin^{2} x style for positive integer powers of named functions
        if (b.type === 'func' && isInt(e) && e.n > 0 && b.name !== 'abs' && b.name !== 'sqrt' && b.name !== 'cbrt') {
          return funcHead(b, o) + '^{' + et + '}' + funcArgTex(b, o);
        }
        let bt = tex(b, o);
        const wrap = ['add', 'mul', 'div', 'neg', 'pow', 'func'].includes(b.type) && !(b.type === 'func' && b.name === 'abs') ||
          (b.type === 'num' && (b.n < 0 || b.d !== 1 || b.f));
        if (wrap) bt = paren(bt);
        return bt + '^{' + et + '}';
      }
      case 'func': {
        const a = n.arg;
        if (n.name === 'sqrt') return '\\sqrt{' + tex(a, o) + '}';
        if (n.name === 'cbrt') return '\\sqrt[3]{' + tex(a, o) + '}';
        if (n.name === 'abs') return '\\left|' + tex(a, o) + '\\right|';
        if (n.name === 'exp') return 'e^{' + tex(a, o) + '}';
        return funcHead(n, o) + funcArgTex(n, o);
      }
    }
    return '?';
  }
  // Decide whether two adjacent factors need an explicit \cdot to stay readable.
  function needsCdot(prev, cur, curTex) {
    if (/^[0-9.]/.test(curTex) || curTex.startsWith('-')) return true;          // 2·3, x·2
    if (cur.type === 'div' && (prev.type === 'num' || prev.type === 'div')) return true; // 2·\frac{1}{x}
    if (prev.type === 'func' && bareArg(prev.arg) && cur.type !== 'func') return true; // \sin x · x
    if (prev.type === 'pow' && prev.base.type === 'func' && bareArg(prev.base.arg) && cur.type !== 'func') return true;
    if (cur.type === 'num' && prev.type !== 'num') return true;
    const vb = (x) => (x.type === 'var' ? x.name : x.type === 'pow' && x.base.type === 'var' ? x.base.name : null);
    if (vb(prev) && vb(prev) === vb(cur)) return true;                           // x·x^2
    return false;
  }

  /* ---------------- Plain-text printing (for URLs, input box, tests) ---------------- */
  function str(n) {
    switch (n.type) {
      case 'num': return n.f ? strFloat(n.n) : (n.d === 1 ? String(n.n) : n.n + '/' + n.d);
      case 'const': return n.name;
      case 'var': return n.name;
      case 'add': return n.terms.map((t, i) => { const s = str(t); return i === 0 ? s : s.startsWith('-') ? ' - ' + s.slice(1) : ' + ' + s; }).join('');
      case 'mul': return n.factors.map((f) => (f.type === 'add' || f.type === 'neg' || (f.type === 'num' && f.d !== 1) ? '(' + str(f) + ')' : str(f))).join('*');
      case 'div': return wrapS(n.num) + '/' + wrapS(n.den);
      case 'pow': return wrapS(n.base) + '^' + wrapS(n.exp);
      case 'neg': return '-' + wrapS(n.arg);
      case 'func': return n.name === 'log' && n.base ? 'log(' + str(n.base) + ', ' + str(n.arg) + ')' : n.name + '(' + str(n.arg) + ')';
    }
    return '?';
  }
  function wrapS(n) {
    const s = str(n);
    return n.type === 'num' && n.d === 1 && n.n >= 0 && !/[*^]/.test(s) || n.type === 'var' || n.type === 'const' || n.type === 'func' ? s : '(' + s + ')';
  }

  Object.assign(Calc, {
    gcd, num, radd, rmul, rneg, rinv, rpowInt, rval, isFloat,
    isNum, isZero, isOne, isInt, isNeg, numEq,
    C, V, add, mul, mulDot, div, pow, neg, fn, TEX,
    children, contains, isConstant, freeVars, key, evaluate, tex, str, paren,
    FN_EVAL, FN_TEX,
  });
})(typeof window !== 'undefined' ? window : globalThis);
