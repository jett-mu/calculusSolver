/* parser.js — tokenizer + recursive-descent parser producing display ASTs.
 * Supports implicit multiplication (2x, x sin x, (x+1)(x-1)), function powers (sin^2 x),
 * inverse notation (sin^-1 x), |x|, log_b(x), log(b, x), unicode (π, √, ·, ×, −, ÷). */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const { num, C, V, add, mul, div, pow, neg, fn } = Calc;

  class ParseError extends Error {
    constructor(message, pos) { super(message); this.pos = pos; }
  }

  // alias → canonical function name
  const FUNCS = {
    sin: 'sin', cos: 'cos', tan: 'tan', cot: 'cot', sec: 'sec', csc: 'csc', cosec: 'csc',
    arcsin: 'asin', asin: 'asin', arccos: 'acos', acos: 'acos', arctan: 'atan', atan: 'atan',
    arccot: 'acot', acot: 'acot', arcsec: 'asec', asec: 'asec', arccsc: 'acsc', acsc: 'acsc',
    sinh: 'sinh', cosh: 'cosh', tanh: 'tanh', coth: 'coth', sech: 'sech', csch: 'csch',
    arcsinh: 'asinh', arsinh: 'asinh', asinh: 'asinh',
    arccosh: 'acosh', arcosh: 'acosh', acosh: 'acosh',
    arctanh: 'atanh', artanh: 'atanh', atanh: 'atanh',
    arccoth: 'acoth', arcoth: 'acoth', acoth: 'acoth',
    arcsech: 'asech', arsech: 'asech', asech: 'asech',
    arccsch: 'acsch', arcsch: 'acsch', acsch: 'acsch',
    ln: 'ln', log: 'log', exp: 'exp', sqrt: 'sqrt', cbrt: 'cbrt', abs: 'abs',
  };
  const INVERSE = {
    sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot', sec: 'asec', csc: 'acsc',
    sinh: 'asinh', cosh: 'acosh', tanh: 'atanh', coth: 'acoth', sech: 'asech', csch: 'acsch',
  };
  const WORDS = Object.keys(FUNCS).concat(['pi', 'theta', 'alpha', 'beta', 'phi', 'omega']).sort((a, b) => b.length - a.length);

  function tokenize(src) {
    const toks = [];
    let i = 0;
    const push = (t, v, pos) => toks.push({ t, v, pos });
    while (i < src.length) {
      const ch = src[i];
      if (/\s/.test(ch)) { i++; continue; }
      if (/[0-9.]/.test(ch)) {
        const m = /^(\d+\.?\d*|\.\d+)/.exec(src.slice(i));
        if (!m) throw new ParseError("I couldn't read the number here", i);
        const s = m[1];
        const parts = s.split('.');
        const frac = parts[1] || '';
        const digits = (parts[0] || '') + frac;
        let node;
        if (digits.length <= 15) node = num(parseInt(digits || '0', 10), Math.pow(10, frac.length));
        else node = { type: 'num', n: parseFloat(s), d: 1, f: true };
        push('num', node, i);
        i += s.length;
        continue;
      }
      if (/[A-Za-z]/.test(ch)) {
        // split a run of letters greedily into known words / single letters
        const m = /^[A-Za-z]+/.exec(src.slice(i));
        const run = m[0];
        let j = 0;
        while (j < run.length) {
          const rest = run.slice(j).toLowerCase();
          const w = WORDS.find((w) => rest.startsWith(w));
          if (w) {
            if (FUNCS[w]) push('fn', FUNCS[w], i + j);
            else if (w === 'pi') push('const', 'pi', i + j);
            else push('var', w, i + j);
            j += w.length;
          } else {
            const c = run[j];
            if (c === 'e') push('const', 'e', i + j);
            else push('var', c, i + j);
            j++;
          }
        }
        i += run.length;
        continue;
      }
      const map = {
        '+': ['op', '+'], '-': ['op', '-'], '−': ['op', '-'], '–': ['op', '-'],
        '*': ['op', '*'], '·': ['op', '*'], '×': ['op', '*'], '⋅': ['op', '*'],
        '/': ['op', '/'], '÷': ['op', '/'], '^': ['op', '^'],
        '(': ['(', '('], '[': ['(', '('], '{': ['(', '('],
        ')': [')', ')'], ']': [')', ')'], '}': [')', ')'],
        '|': ['|', '|'], ',': [',', ','], '_': ['_', '_'],
        'π': ['const', 'pi'], '√': ['fn', 'sqrt'], '∛': ['fn', 'cbrt'], 'θ': ['var', 'theta'],
        '²': ['sup', 2], '³': ['sup', 3],
      };
      if (ch === '*' && src[i + 1] === '*') { push('op', '^', i); i += 2; continue; }
      if (map[ch]) { push(map[ch][0], map[ch][1], i); i++; continue; }
      throw new ParseError("I don't recognise the character “" + ch + '”', i);
    }
    push('end', null, src.length);
    return toks;
  }

  function parse(src) {
    if (!src || !src.trim()) throw new ParseError('Type a function to differentiate', 0);
    const toks = tokenize(src);
    let p = 0;
    let absDepth = 0;
    const peek = () => toks[p];
    const next = () => toks[p++];
    const isOp = (v) => peek().t === 'op' && peek().v === v;
    const describe = (t) => (t.t === 'end' ? 'the end of the input' : '“' + (t.t === 'num' ? Calc.str(t.v) : t.v) + '”');
    function expect(t, what) {
      if (peek().t !== t) {
        throw new ParseError('Expected ' + what + ' but found ' + describe(peek()), peek().pos);
      }
      return next();
    }
    const startsFactor = () => {
      const t = peek().t;
      return t === 'num' || t === 'var' || t === 'const' || t === 'fn' || t === '(' || (t === '|' && absDepth === 0);
    };
    const fold = (n) => (n.type === 'neg' && n.arg.type === 'num' ? num(-n.arg.n, n.arg.d) : n);
    const append = (acc, f) => (acc.type === 'mul' && !acc._paren ? mul(acc.factors.concat([f])) : mul([acc, f]));

    function parseExpr() {
      const terms = [parseTerm()];
      while (isOp('+') || isOp('-')) {
        const op = next().v;
        const t = parseTerm();
        terms.push(op === '-' ? fold(neg(t)) : t);
      }
      return terms.length === 1 ? terms[0] : add(terms);
    }
    function parseTerm() {
      let acc = parseUnary();
      for (;;) {
        if (isOp('*')) { next(); acc = append(acc, parseUnary()); }
        else if (isOp('/')) { next(); acc = div(acc, parseUnary()); }
        else if (startsFactor()) { acc = append(acc, parsePower()); }
        else break;
      }
      return acc;
    }
    function parseUnary() {
      if (isOp('-')) { next(); return fold(neg(parseUnary())); }
      if (isOp('+')) { next(); return parseUnary(); }
      return parsePower();
    }
    function parseExponent() {
      if (isOp('-')) { next(); return fold(neg(parseExponent())); }
      if (isOp('+')) { next(); return parseExponent(); }
      const b = parsePrimary();
      if (isOp('^')) { next(); return pow(b, parseExponent()); }
      return b;
    }
    function parsePower() {
      const b = parsePrimary();
      if (isOp('^')) { next(); return pow(b, parseExponent()); }
      if (peek().t === 'sup') return pow(b, num(next().v));
      return b;
    }
    function parsePrimary() {
      const t = peek();
      switch (t.t) {
        case 'num': next(); return t.v;
        case 'const': next(); return C(t.v);
        case 'var': next(); return V(t.v);
        case '(': {
          next();
          if (peek().t === ')') throw new ParseError('Empty parentheses', peek().pos);
          const e = parseExpr();
          expect(')', 'a closing parenthesis');
          if (e.type === 'mul') e._paren = true;
          return e;
        }
        case '|': {
          next(); absDepth++;
          const e = parseExpr();
          absDepth--;
          expect('|', 'a closing “|”');
          return fn('abs', e);
        }
        case 'fn': return parseFunction();
        case 'end': throw new ParseError('The expression ends too early', t.pos);
        default: throw new ParseError('Unexpected ' + describe(t), t.pos);
      }
    }
    function parseFunction() {
      const tok = next();
      let name = tok.v;
      let base = null;
      let fpow = null;
      if (name === 'log' && peek().t === '_') {
        next();
        base = parsePrimary();
      }
      if (isOp('^')) {
        next();
        const e = parseExponent();
        const isMinusOne = e.type === 'num' && e.n === -1 && e.d === 1;
        if (isMinusOne && INVERSE[name]) name = INVERSE[name];
        else fpow = e;
      } else if (peek().t === 'sup') fpow = num(next().v);
      let arg;
      if (peek().t === '(') {
        next();
        if (peek().t === ')') throw new ParseError('The function ' + name + ' needs an argument', peek().pos);
        arg = parseExpr();
        if (name === 'log' && !base && peek().t === ',') { next(); base = arg; arg = parseExpr(); }
        expect(')', 'a closing parenthesis');
      } else {
        // implicit argument: sin x, sin 2x, ln x^2, sqrt x — stops at the next function or operator
        if (!startsFactor() && !isOp('-')) {
          throw new ParseError('The function ' + name + ' needs an argument', peek().pos);
        }
        let neg1 = false;
        if (isOp('-')) { next(); neg1 = true; }
        arg = parsePower();
        while (startsFactor() && peek().t !== 'fn') arg = append(arg, parsePower());
        if (neg1) arg = fold(neg(arg));
      }
      let node = fn(name, arg, base || undefined);
      if (fpow) node = pow(node, fpow);
      return node;
    }

    const tree = parseExpr();
    if (peek().t !== 'end') {
      const t = peek();
      if (t.t === ')') throw new ParseError('There is an extra closing parenthesis', t.pos);
      throw new ParseError('Unexpected ' + describe(t), t.pos);
    }
    return strip(tree);
  }
  function strip(n) {
    if (n._paren) delete n._paren;
    Calc.children(n).forEach(strip);
    return n;
  }

  Object.assign(Calc, { parse, tokenize, ParseError, FUNC_ALIASES: FUNCS });
})(typeof window !== 'undefined' ? window : globalThis);
