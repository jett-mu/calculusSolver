/* derive.js — step-tracing symbolic differentiator.
 *
 * derive(tree, v) returns a Step:
 *   { exprTex, rules:[ruleId...], formula, where, setup, children:[Step], combinedTex, result, resultTex }
 *   formula   – the general rule being applied (LaTeX)
 *   where     – substitutions such as "u = x^2"
 *   setup     – the rule applied to this expression, with d/dx[...] placeholders for sub-derivatives
 *   children  – the sub-derivatives, each a Step
 *   combined  – setup with the children's answers substituted, before simplifying
 *   result    – simplified canonical tree (resultTex is its LaTeX) */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const { num, C, V, add, mul, mulDot, div, pow, neg, fn, TEX, tex, isConstant, isOne, isNum, simplify, present, texOf } = Calc;
  const ONE = num(1), TWO = num(2), ZERO = num(0);

  let X = 'x';
  const dx = () => '\\frac{d}{d' + vtex() + '}';
  const vtex = () => tex(V(X));
  const dd = (n) => dx() + '\\left[' + tex(n) + '\\right]';
  const DD = (n) => TEX(dd(n));
  const sq = (u) => pow(u, TWO);
  const sub = (a, b) => add([a, neg(b)]);
  const R = (step) => present(step.result);

  // f'(u) for each named function, as display trees
  const OUTER = {
    sin: (u) => fn('cos', u),
    cos: (u) => neg(fn('sin', u)),
    tan: (u) => sq(fn('sec', u)),
    cot: (u) => neg(sq(fn('csc', u))),
    sec: (u) => mul([fn('sec', u), fn('tan', u)]),
    csc: (u) => neg(mul([fn('csc', u), fn('cot', u)])),
    asin: (u) => div(ONE, fn('sqrt', sub(ONE, sq(u)))),
    acos: (u) => neg(div(ONE, fn('sqrt', sub(ONE, sq(u))))),
    atan: (u) => div(ONE, add([ONE, sq(u)])),
    acot: (u) => neg(div(ONE, add([ONE, sq(u)]))),
    asec: (u) => div(ONE, mul([fn('abs', u), fn('sqrt', sub(sq(u), ONE))])),
    acsc: (u) => neg(div(ONE, mul([fn('abs', u), fn('sqrt', sub(sq(u), ONE))]))),
    sinh: (u) => fn('cosh', u),
    cosh: (u) => fn('sinh', u),
    tanh: (u) => sq(fn('sech', u)),
    coth: (u) => neg(sq(fn('csch', u))),
    sech: (u) => neg(mul([fn('sech', u), fn('tanh', u)])),
    csch: (u) => neg(mul([fn('csch', u), fn('coth', u)])),
    asinh: (u) => div(ONE, fn('sqrt', add([sq(u), ONE]))),
    acosh: (u) => div(ONE, fn('sqrt', sub(sq(u), ONE))),
    atanh: (u) => div(ONE, sub(ONE, sq(u))),
    acoth: (u) => div(ONE, sub(ONE, sq(u))),
    asech: (u) => neg(div(ONE, mul([u, fn('sqrt', sub(ONE, sq(u)))]))),
    acsch: (u) => neg(div(ONE, mul([fn('abs', u), fn('sqrt', add([ONE, sq(u)]))]))),
    ln: (u) => div(ONE, u),
    lnabs: (u) => div(ONE, u),
    exp: (u) => fn('exp', u),
    sqrt: (u) => div(ONE, mul([TWO, fn('sqrt', u)])),
    cbrt: (u) => div(ONE, mul([num(3), fn('cbrt', sq(u))])),
    abs: (u) => div(u, fn('abs', u)),
  };
  const RULE_OF = { ln: 'ln', lnabs: 'lnAbs', exp: 'exp', log: 'logA' };
  const ruleOf = (name) => RULE_OF[name] || name;

  function mk(n) { return { expr: n, exprTex: tex(n), rules: [], children: [] }; }
  function fin(st, raw, resultNode) {
    if (raw) {
      st.combinedTex = tex(raw);
      st.result = simplify(raw);
    } else st.result = resultNode;
    st.resultTex = texOf(st.result);
    const bare = (t) => t.replace(/ \\cdot /g, '');
    if (st.combinedTex && bare(st.combinedTex) === bare(st.resultTex)) st.combinedTex = null;
    return st;
  }
  const texParen = (n) => (n.type === 'add' || n.type === 'neg' ? Calc.paren(tex(n)) : tex(n));

  function D(n) {
    const st = mk(n);
    if (isConstant(n, X)) {
      st.rules = ['constant'];
      st.formula = dx() + '\\,c = 0';
      return fin(st, null, ZERO);
    }
    switch (n.type) {
      case 'var':
        st.rules = ['identity'];
        st.formula = dx() + '\\,' + vtex() + ' = 1';
        return fin(st, null, ONE);
      case 'neg': {
        st.rules = ['constMult'];
        st.formula = dx() + '\\left[-f\\right] = -' + dx() + '\\left[f\\right]';
        const c = D(n.arg);
        st.children = [c];
        st.setup = '-' + dd(n.arg);
        return fin(st, neg(R(c)));
      }
      case 'add': return dAdd(n, st);
      case 'mul': return dMul(n, st);
      case 'div': return dDiv(n, st);
      case 'pow': return dPow(n, st);
      case 'func': return dFunc(n, st);
    }
    throw new Error('Cannot differentiate ' + n.type);
  }

  function dAdd(n, st) {
    st.rules = ['sum'];
    st.formula = dx() + '\\left[f \\pm g\\right] = ' + dx() + 'f \\pm ' + dx() + 'g';
    const parts = n.terms.map((t) => (t.type === 'neg' ? { sign: -1, t: t.arg }
      : isNum(t) && t.n < 0 ? { sign: -1, t: Calc.rneg(t) } : { sign: 1, t }));
    st.children = parts.map((p) => D(p.t));
    st.setup = tex(add(parts.map((p) => (p.sign < 0 ? neg(DD(p.t)) : DD(p.t)))));
    const raw = add(parts.map((p, i) => (p.sign < 0 ? neg(R(st.children[i])) : R(st.children[i]))));
    return fin(st, raw);
  }

  function dMul(n, st) {
    const cs = n.factors.filter((f) => isConstant(f, X));
    const ns = n.factors.filter((f) => !isConstant(f, X));
    const one = (arr) => (arr.length === 1 ? arr[0] : mul(arr));
    if (cs.length) {
      const c = one(cs), rest = one(ns);
      st.rules = ['constMult'];
      st.formula = dx() + '\\left[c\\,f\\right] = c\\,' + dx() + 'f';
      st.where = 'c = ' + tex(c);
      const ch = D(rest);
      st.children = [ch];
      st.setup = tex(mulDot([c, DD(rest)]));
      return fin(st, mulDot([c, R(ch)]));
    }
    st.rules = ['product'];
    const letters = ['f', 'g', 'h', 'k', 'm', 'p'];
    const k = ns.length;
    if (k <= letters.length) {
      const L = letters.slice(0, k);
      const lhs = L.join('');
      const rhs = L.map((_, i) => L.map((l, j) => (i === j ? l + "'" : l)).join('')).join(' + ');
      st.formula = '(' + lhs + ")' = " + rhs;
    } else st.formula = "(f_1 f_2 \\cdots f_n)' = \\sum_i f_1 \\cdots f_i' \\cdots f_n";
    st.children = ns.map(D);
    st.setup = tex(add(ns.map((_, i) => mulDot(ns.map((f, j) => (i === j ? DD(f) : f))))));
    const raw = add(ns.map((_, i) => mulDot(ns.map((f, j) => (i === j ? R(st.children[i]) : f)))));
    return fin(st, raw);
  }

  function dDiv(n, st) {
    const f = n.num, g = n.den;
    if (isConstant(g, X)) {
      st.rules = ['constMult'];
      st.formula = dx() + '\\left[\\frac{f}{c}\\right] = \\frac{1}{c}\\,' + dx() + 'f';
      st.where = 'c = ' + tex(g);
      const ch = D(f);
      st.children = [ch];
      st.setup = tex(div(DD(f), g));
      return fin(st, div(R(ch), g));
    }
    if (isConstant(f, X)) {
      st.rules = isOne(f) ? ['reciprocal'] : ['constMult', 'reciprocal'];
      st.formula = dx() + "\\left[\\frac{c}{g}\\right] = -\\frac{c\\,g'}{g^{2}}";
      st.where = (isOne(f) ? '' : 'c = ' + tex(f) + ',\\; ') + 'g = ' + tex(g);
      const ch = D(g);
      st.children = [ch];
      const top = (d) => (isOne(f) ? d : mulDot([f, d]));
      st.setup = tex(neg(div(top(DD(g)), sq(g))));
      return fin(st, neg(div(top(R(ch)), sq(g))));
    }
    st.rules = ['quotient'];
    st.formula = "\\left(\\frac{f}{g}\\right)' = \\frac{f'g - fg'}{g^{2}}";
    st.where = 'f = ' + tex(f) + ',\\; g = ' + tex(g);
    const cf = D(f), cg = D(g);
    st.children = [cf, cg];
    st.setup = tex(div(sub(mulDot([DD(f), g]), mulDot([f, DD(g)])), sq(g)));
    return fin(st, div(sub(mulDot([R(cf), g]), mulDot([f, R(cg)])), sq(g)));
  }

  function dPow(n, st) {
    const b = n.base, e = n.exp;
    const bc = isConstant(b, X), ec = isConstant(e, X);
    const isVar = b.type === 'var' && b.name === X;
    if (!bc && ec) {
      const em1 = present(simplify(sub(e, ONE)));
      const pw = (base) => (isOne(simplify(em1)) ? base : pow(base, em1));
      const setupPow = pow(b, TEX(tex(e) + ' - 1'));
      if (isVar) {
        st.rules = ['power'];
        st.formula = dx() + '\\,' + vtex() + '^{n} = n\\,' + vtex() + '^{n-1}';
        st.where = 'n = ' + tex(e);
        st.setup = tex(mul([e, setupPow]));
        return fin(st, mulDot([e, pw(b)]));
      }
      st.rules = ['power', 'chain'];
      st.formula = dx() + '\\,u^{n} = n\\,u^{n-1}\\cdot\\frac{du}{d' + vtex() + '}';
      st.where = 'u = ' + tex(b) + ',\\; n = ' + tex(e);
      const ch = D(b);
      st.children = [ch];
      st.setup = tex(mulDot([e, setupPow, DD(b)]));
      return fin(st, mulDot([e, pw(b), R(ch)]));
    }
    if (bc && !ec) {
      const chain = !(e.type === 'var' && e.name === X);
      const isE = b.type === 'const' && b.name === 'e';
      st.rules = isE ? ['exp'] : ['expA'];
      if (chain) st.rules.push('chain');
      const U = chain ? V('u') : V(X);
      const outer = (u) => (isE ? pow(C('e'), u) : mul([pow(b, u), fn('ln', b)]));
      st.formula = dx() + '\\,' + tex(pow(isE ? C('e') : V('a'), U)) + ' = ' +
        tex(isE ? pow(C('e'), U) : mul([pow(V('a'), U), fn('ln', V('a'))])) + (chain ? '\\cdot\\frac{du}{d' + vtex() + '}' : '');
      if (!isE) st.where = 'a = ' + tex(b) + (chain ? ',\\; u = ' + tex(e) : '');
      else if (chain) st.where = 'u = ' + tex(e);
      if (!chain) return fin(st, outer(e));
      const ch = D(e);
      st.children = [ch];
      const o = outer(e);
      st.setup = tex(mulDot((o.type === 'mul' ? o.factors : [o]).concat([DD(e)])));
      return fin(st, mulDot((o.type === 'mul' ? o.factors : [o]).concat([R(ch)])));
    }
    // f(x)^g(x): logarithmic differentiation
    st.rules = ['genPow', 'logDiff'];
    st.formula = "y = f^{g} \\;\\Rightarrow\\; \\ln y = g\\ln f \\;\\Rightarrow\\; y' = f^{g}\\,\\left(g\\ln f\\right)'";
    const inner = mul([e, fn('ln', b)]);
    st.where = '\\ln y = ' + tex(inner);
    const ch = D(inner);
    st.children = [ch];
    st.setup = tex(mulDot([n, DD(inner)]));
    return fin(st, mulDot([n, R(ch)]));
  }

  function dFunc(n, st) {
    let name = n.name, arg = n.arg;
    if (name === 'log') {
      const base = n.base || num(10);
      if (!isConstant(base, X)) {
        // change of base: log_b(u) = ln u / ln b
        st.rules = ['logA', 'quotient'];
        st.formula = '\\log_{b} u = \\frac{\\ln u}{\\ln b}';
        const rewritten = div(fn('ln', arg), fn('ln', base));
        const ch = D(rewritten);
        st.children = [ch];
        st.setup = dd(rewritten);
        return fin(st, R(ch));
      }
      const chain = !(arg.type === 'var' && arg.name === X);
      st.rules = chain ? ['logA', 'chain'] : ['logA'];
      const U = chain ? V('u') : V(X);
      const outer = (u) => div(ONE, mul([u, fn('ln', base)]));
      st.formula = dx() + tex(fn('log', U, base)) + ' = ' + tex(outer(U)) + (chain ? '\\cdot\\frac{du}{d' + vtex() + '}' : '');
      if (chain) st.where = 'u = ' + tex(arg);
      if (!chain) return fin(st, outer(arg));
      const ch = D(arg);
      st.children = [ch];
      st.setup = tex(mulDot([outer(arg), DD(arg)]));
      return fin(st, mulDot([outer(arg), R(ch)]));
    }
    if (name === 'ln' && arg.type === 'func' && arg.name === 'abs') { name = 'lnabs'; arg = arg.arg; }
    const outerFn = OUTER[name];
    if (!outerFn) throw new Error('No derivative rule for ' + name);
    const shown = (u) => (name === 'lnabs' ? fn('ln', fn('abs', u)) : fn(name, u));
    const chain = !(arg.type === 'var' && arg.name === X);
    st.rules = chain ? [ruleOf(name), 'chain'] : [ruleOf(name)];
    const U = chain ? V('u') : V(X);
    st.formula = dx() + tex(shown(U)) + ' = ' + tex(outerFn(U)) + (chain ? '\\cdot\\frac{du}{d' + vtex() + '}' : '');
    if (!chain) return fin(st, outerFn(arg));
    st.where = 'u = ' + tex(arg);
    const ch = D(arg);
    st.children = [ch];
    const o = outerFn(arg);
    st.setup = tex(mulDot([o, DD(arg)]));
    return fin(st, mulDot([o, R(ch)]));
  }

  function rulesUsed(step, out) {
    out = out || [];
    step.rules.forEach((r) => { if (!out.includes(r)) out.push(r); });
    step.children.forEach((c) => rulesUsed(c, out));
    return out;
  }

  /* Differentiate `tree` `order` times with respect to `v`. */
  function derive(tree, v, order) {
    X = v || 'x';
    Calc.setVar(X);
    order = order || 1;
    const steps = [];
    let cur = tree;
    for (let i = 0; i < order; i++) {
      const st = D(cur);
      st.order = i + 1;
      steps.push(st);
      cur = present(st.result);
    }
    const result = steps[steps.length - 1].result;
    return { steps, result, resultTex: texOf(result), rules: steps.reduce((a, s) => rulesUsed(s, a), []) };
  }

  Object.assign(Calc, { derive, rulesUsed, OUTER });
})(typeof window !== 'undefined' ? window : globalThis);
