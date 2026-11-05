/* Node test harness:  node tests/run.js
 * 1. Numeric check: every derivative is compared with a central finite difference at random points.
 * 2. Exact-form checks for canonical answers.
 * 3. Parser checks.
 * 4. Math field: text → model → text round trips, keystroke editing, error mapping.
 * 5. Integrals: every antiderivative is differentiated numerically and compared with the integrand;
 *    exact forms, technique tagging, and non-elementary detection. */
const path = require('path');
['ast', 'parser', 'simplify', 'derive', 'integrate', 'rules', 'mathfield'].forEach((f) => require(path.join(__dirname, '..', 'js', f + '.js')));
const Calc = globalThis.Calc;

let pass = 0, fail = 0;
const failures = [];
function ok(cond, msg) { if (cond) pass++; else { fail++; failures.push(msg); } }

// [expression, sampling interval]
const NUMERIC = [
  ['5', [-3, 3]], ['x', [-3, 3]], ['x^2', [-3, 3]], ['x^3 - 2x + 7', [-3, 3]], ['3x^4', [-2, 2]],
  ['x^-2', [0.5, 3]], ['1/x', [0.5, 3]], ['sqrt(x)', [0.3, 4]], ['x^(3/2)', [0.3, 4]], ['cbrt(x)', [0.3, 4]],
  ['x^(1/3)', [-4, -0.3]], ['pi x^2', [-2, 2]], ['a x^2 + b x', [-2, 2]],
  ['(x+1)(x-1)', [-3, 3]], ['x sin x', [-3, 3]], ['x^2 e^x', [-2, 2]], ['x sin x cos x', [-2, 2]],
  ['x/(x+1)', [0, 3]], ['(x^2+1)/(x-3)', [-2, 2]], ['sin x / x', [0.3, 3]], ['3/(x^2+1)', [-2, 2]], ['1/sin x', [0.3, 2.8]],
  ['(x^2+1)^3', [-2, 2]], ['sin(x^2)', [-2, 2]], ['cos(3x+1)', [-2, 2]], ['sqrt(1-x^2)', [-0.9, 0.9]],
  ['e^x', [-2, 2]], ['e^(2x)', [-2, 2]], ['e^(-x^2)', [-2, 2]], ['2^x', [-2, 2]], ['10^(x^2)', [-1, 1]], ['exp(sin x)', [-2, 2]],
  ['ln x', [0.2, 4]], ['ln(x^2+1)', [-2, 2]], ['ln|x|', [-4, -0.2]], ['ln(abs(x^3))', [0.3, 3]], ['log x', [0.2, 4]], ['log_2(x)', [0.2, 4]],
  ['log(3, x^2+1)', [-2, 2]], ['log_x(5)', [1.5, 4]],
  ['sin x', [-3, 3]], ['cos x', [-3, 3]], ['tan x', [-1.2, 1.2]], ['cot x', [0.3, 2.8]], ['sec x', [-1.2, 1.2]], ['csc x', [0.3, 2.8]],
  ['sin^2 x', [-3, 3]], ['tan(x)^3', [-1, 1]], ['ln(sec x + tan x)', [-1.2, 1.2]], ['sin(cos(x))', [-3, 3]],
  ['arcsin x', [-0.9, 0.9]], ['arccos x', [-0.9, 0.9]], ['arctan x', [-3, 3]], ['arccot x', [-3, 3]],
  ['arcsec x', [1.2, 4]], ['arcsec x', [-4, -1.2]], ['arccsc x', [1.2, 4]], ['arccsc x', [-4, -1.2]],
  ['arctan(1/x)', [0.3, 3]], ['arcsin(2x)', [-0.4, 0.4]], ['sin^-1 x', [-0.9, 0.9]],
  ['sinh x', [-2, 2]], ['cosh x', [-2, 2]], ['tanh x', [-2, 2]], ['coth x', [0.3, 3]], ['sech x', [-2, 2]], ['csch x', [0.3, 3]],
  ['arsinh x', [-3, 3]], ['arcosh x', [1.2, 4]], ['artanh x', [-0.9, 0.9]], ['arcoth x', [1.2, 4]],
  ['arsech x', [0.1, 0.9]], ['arcsch x', [0.3, 3]], ['arcsch x', [-3, -0.3]], ['cosh(x^2)', [-1, 1]],
  ['|x|', [0.2, 3]], ['|x|', [-3, -0.2]], ['|x^2 - 4|', [-1.5, 1.5]], ['abs(sin x)', [0.2, 3]],
  ['x^x', [0.2, 3]], ['x^(sin x)', [0.2, 3]], ['(sin x)^x', [0.2, 3]], ['x^(1/x)', [0.3, 4]],
  ['e^x cos x', [-2, 2]], ['e^x sin x / (1 + x^2)', [-2, 2]], ['sqrt(x) ln x', [0.3, 4]], ['(x^2 - 1)^(1/2)', [1.2, 4]],
  ['-x^2 + 3x - 1', [-2, 2]], ['-(sin x)', [-2, 2]], ['2 sin x cos x', [-2, 2]], ['x^2 sin(1/x)', [0.3, 3]],
  ['tan(sin(e^x))', [-1, 0.2]], ['ln(ln x)', [1.5, 5]], ['1/(2 sqrt x)', [0.3, 4]], ['x/sqrt(x^2+1)', [-2, 2]],
];

function rand(a, b) { return a + Math.random() * (b - a); }
const ENV_CONST = { a: 1.7, b: -0.6, c: 2.3 };

for (const [src, [lo, hi]] of NUMERIC) {
  let tree, res;
  try {
    tree = Calc.parse(src);
    res = Calc.derive(tree, 'x', 1);
  } catch (e) { ok(false, src + ' threw: ' + e.message + '\n' + e.stack); continue; }
  let good = true, detail = '';
  for (let i = 0; i < 6; i++) {
    const x = rand(lo, hi);
    const h = 1e-5;
    const f = (t) => Calc.evaluate(tree, Object.assign({ x: t }, ENV_CONST));
    const fd = (f(x + h) - f(x - h)) / (2 * h);
    const got = Calc.evaluate(res.result, Object.assign({ x }, ENV_CONST));
    const tol = 1e-4 * Math.max(1, Math.abs(fd));
    if (!isFinite(fd)) continue;
    if (!(Math.abs(got - fd) <= tol)) { good = false; detail = `x=${x.toFixed(4)} expected ${fd} got ${got}`; break; }
  }
  ok(good, `numeric ${src}: ${detail}  [result: ${res.resultTex}]`);
}

// second derivatives: numeric check too
for (const src of ['x^4', 'sin x', 'e^(x^2)', 'x ln x', '1/(1+x^2)']) {
  const tree = Calc.parse(src);
  const res = Calc.derive(tree, 'x', 2);
  const x = 0.7, h = 1e-4;
  const f = (t) => Calc.evaluate(tree, { x: t });
  const fd2 = (f(x + h) - 2 * f(x) + f(x - h)) / (h * h);
  const got = Calc.evaluate(res.result, { x });
  ok(Math.abs(got - fd2) < 1e-3 * Math.max(1, Math.abs(fd2)), `2nd derivative ${src}: expected ${fd2} got ${got}`);
}

// exact LaTeX forms
const EXACT = [
  ['x^2', '2x'], ['x^3', '3x^{2}'], ['5x', '5'], ['7', '0'], ['sin x', '\\cos x'], ['cos x', '-\\sin x'],
  ['e^x', 'e^{x}'], ['ln x', '\\frac{1}{x}'], ['x^x', 'x^{x}\\left(\\ln x + 1\\right)'],
  ['sqrt x', '\\frac{1}{2\\sqrt{x}}'], ['tan x', '\\sec^{2} x'], ['sin(x^2)', '2x\\cos\\left(x^{2}\\right)'],
  ['x/(x+1)', '\\frac{1}{\\left(x + 1\\right)^{2}}'], ['ln(sec x + tan x)', '\\sec x'], ['arctan x', '\\frac{1}{x^{2} + 1}'],
  ['2^x', '2^{x}\\ln 2'], ['(x+1)(x-1)', '2x'], ['sin x / cos x', '\\frac{1}{\\cos^{2} x}'], ['|x|', '\\frac{x}{\\left|x\\right|}'],
  ['ln|x|', '\\frac{1}{x}'], ['x^2 + 3x + 2', '2x + 3'], ['1/x', '-\\frac{1}{x^{2}}'], ['e^(2x)', '2e^{2x}'],
];
for (const [src, want] of EXACT) {
  let got;
  try { got = Calc.derive(Calc.parse(src), 'x', 1).resultTex; } catch (e) { got = 'ERR ' + e.message; }
  ok(got === want, `exact ${src}: want ${want}  got ${got}`);
}

// rule chips
const RULES = [['x^2', ['power']], ['sin(x^2)', ['sin', 'chain', 'power']], ['x sin x', ['product']], ['x/(x+1)', ['quotient']], ['x^x', ['genPow', 'logDiff']]];
for (const [src, want] of RULES) {
  const got = Calc.derive(Calc.parse(src), 'x', 1).rules;
  ok(want.every((r) => got.includes(r)), `rules ${src}: want ${want} got ${got}`);
}

// parser
const PARSE = [
  ['2x', '2*x'], ['3(x+1)', '3*(x + 1)'], ['x sin x', 'x*sin(x)'], ['sin^2 x', 'sin(x)^2'], ['sin x^2', 'sin(x^2)'],
  ['sin 2x cos x', 'sin(2*x)*cos(x)'], ['2pi x', '2*pi*x'], ['e^-x', 'e^(-x)'], ['log_2 x', 'log(2, x)'], ['|x|', 'abs(x)'],
  ['sin^-1 x', 'asin(x)'], ['x**2', 'x^2'], ['√x', 'sqrt(x)'], ['(x+1)(x-1)', '(x + 1)*(x - 1)'], ['xe^x', 'x*e^x'],
];
for (const [src, want] of PARSE) {
  let got;
  try { got = Calc.str(Calc.parse(src)); } catch (e) { got = 'ERR ' + e.message; }
  ok(got === want, `parse ${src}: want ${want} got ${got}`);
}
for (const bad of ['', '(x+1', 'x+', 'sin()', '2 $ x', 'x)']) {
  let threw = false;
  try { Calc.parse(bad); } catch (e) { threw = e instanceof Calc.ParseError; }
  ok(threw, `parse error expected for "${bad}"`);
}

/* ---------------- integrals ---------------- */
// [integrand, sampling interval]: d/dx F must equal f on the interval
const INTEGRALS = [
  // basics and table
  ['7', [-3, 3]], ['x', [-3, 3]], ['x^5', [-2, 2]], ['3x^2 - 4x + 1', [-3, 3]], ['sqrt(x)', [0.2, 4]], ['x^(-3)', [0.3, 3]], ['1/x', [0.2, 4]],
  ['1/x', [-4, -0.2]], ['e^x', [-2, 2]], ['2^x', [-2, 2]], ['sin x', [-3, 3]], ['cos x', [-3, 3]], ['sec(x)^2', [-1.2, 1.2]], ['csc(x)^2', [0.3, 2.8]],
  ['sec x tan x', [-1.2, 1.2]], ['csc x cot x', [0.3, 2.8]], ['tan x', [-1.2, 1.2]], ['cot x', [0.3, 2.8]], ['sec x', [-1.2, 1.2]], ['csc x', [0.3, 2.8]],
  ['sinh x', [-2, 2]], ['cosh x', [-2, 2]], ['tanh x', [-2, 2]], ['coth x', [0.3, 3]], ['sech x', [-2, 2]], ['csch x', [0.3, 3]], ['sech(x)^2', [-2, 2]],
  ['|x|', [-3, 3]], ['1/(x^2+4)', [-3, 3]], ['1/sqrt(4-x^2)', [-1.9, 1.9]], ['1/sqrt(x^2+9)', [-3, 3]], ['1/(x sqrt(x^2-1))', [1.2, 4]],
  ['1/(x sqrt(x^2-1))', [-4, -1.2]], ['1/(x^2-3)', [-1.5, 1.5]], ['1/(2x^2+3)', [-2, 2]], ['a x^2 + b', [-2, 2]], ['x^n', [0.3, 3]], ['1/(x^2+a^2)', [-3, 3]],
  // linear substitution
  ['e^(3x)', [-1, 1]], ['sin(2x)', [-2, 2]], ['(2x+1)^10', [-1, 0.5]], ['1/(3x-1)', [0.5, 3]], ['sec(2x)^2', [-0.6, 0.6]], ['cos(3x+1)', [-2, 2]],
  // u-substitution and g'/g
  ['x cos(x^2)', [-2, 2]], ['x e^(x^2)', [-1.5, 1.5]], ['(ln x)/x', [0.3, 4]], ['1/(x ln x)', [1.2, 4]], ['x sqrt(x+1)', [-0.9, 3]],
  ['x/(x^2+1)', [-3, 3]], ['(2x+3)/(x^2+3x+2)', [0, 3]], ['e^x/(1+e^x)', [-2, 2]], ['sin(x) e^(cos x)', [-3, 3]], ['x^3 sqrt(1-x^2)', [-0.9, 0.9]],
  ['x/(x^4+1)', [-2, 2]], ['e^x/(e^(2x)+1)', [-2, 2]], ['sqrt(x)/(1+x)', [0.2, 4]], ['sin x cos x', [-3, 3]], ['tan x sec(x)^2', [-1, 1]],
  // by parts
  ['x e^x', [-2, 2]], ['x^3 e^x', [-2, 2]], ['x^2 sin x', [-3, 3]], ['x sin x', [-3, 3]], ['ln x', [0.2, 4]], ['ln(x)^2', [0.2, 4]], ['x ln x', [0.2, 4]],
  ['arctan x', [-3, 3]], ['arcsin x', [-0.9, 0.9]], ['x^2 arctan x', [-2, 2]], ['x arcsin x', [-0.9, 0.9]], ['ln(x^2+1)', [-2, 2]], ['log_2(x)', [0.3, 4]],
  ['e^x sin x', [-2, 2]], ['e^(2x) cos(3x)', [-1, 1]], ['cos(ln x)', [0.3, 4]], ['x^5 e^(x^2)', [-1, 1]], ['x^2 e^(3x)', [-1, 1]],
  // rational functions
  ['1/(x^2-1)', [-0.9, 0.9]], ['1/(x^2(x+1))', [0.2, 3]], ['x/(x+1)^2', [0, 3]], ['1/(x^3+x)', [0.2, 3]], ['(x^3+1)/(x^2+1)', [-2, 2]],
  ['(x^2+1)/x', [0.2, 3]], ['1/(x^2+2x+5)', [-3, 3]], ['1/(x^2+x+1)', [-3, 3]], ['(x+2)/(x^2+2x+5)', [-3, 3]], ['1/(x^4-1)', [-0.9, 0.9]],
  ['(3x+5)/((x-1)(x+2)^2)', [1.2, 3]], ['1/((x^2+1)(x^2+4))', [-2, 2]], ['x^2/(x^2+1)^2', [-2, 2]], ['1/sqrt(x^2+2x+5)', [-3, 3]],
  // trig integrals
  ['sin^3 x', [-3, 3]], ['cos^5 x', [-3, 3]], ['cos^2 x', [-3, 3]], ['sin^4 x', [-3, 3]], ['sin^2 x cos^2 x', [-3, 3]], ['sin(x)^2 cos(x)^3', [-3, 3]],
  ['tan^2 x', [-1.2, 1.2]], ['tan^3 x', [-1.2, 1.2]], ['sec^3 x', [-1.2, 1.2]], ['sec^4 x', [-1.2, 1.2]], ['tan^3 x sec^3 x', [-1.2, 1.2]],
  ['cot^2 x', [0.3, 2.8]], ['csc^3 x', [0.3, 2.8]], ['sin(3x)cos(2x)', [-3, 3]], ['sin x sin(2x)', [-3, 3]], ['cos(x)cos(4x)', [-3, 3]],
  ['sin x/cos^3 x', [-1.2, 1.2]],
  // trig substitution
  ['sqrt(1-x^2)', [-0.9, 0.9]], ['x^2/sqrt(1-x^2)', [-0.9, 0.9]], ['sqrt(4-x^2)/x^2', [0.3, 1.9]], ['sqrt(x^2+1)', [-3, 3]],
  ['1/(x^2+1)^2', [-3, 3]], ['1/(x^2 sqrt(x^2+4))', [0.3, 3]], ['sqrt(x^2-1)', [1.2, 4]],
  // tangent half-angle
  ['1/(1+cos x)', [-2.5, 2.5]], ['1/(2+sin x)', [-1, 1]], ['1/(5+4cos x)', [-2.5, 2.5]],
];
for (const [src, [lo, hi]] of INTEGRALS) {
  let tree, res;
  try { tree = Calc.parse(src); res = Calc.integrate(tree, 'x'); }
  catch (e) { ok(false, 'integral ' + src + ' threw: ' + e.message); continue; }
  let good = true, detail = '', tested = 0;
  for (let i = 0; i < 8; i++) {
    const x = rand(lo, hi), h = 1e-5;
    const env = (t) => Object.assign({ x: t }, ENV_CONST, { n: 2.3 });
    const F = (t) => Calc.evaluate(res.result, env(t));
    const fd = (F(x + h) - F(x - h)) / (2 * h);
    const want = Calc.evaluate(tree, env(x));
    if (!isFinite(fd) || !isFinite(want)) continue;
    tested++;
    if (!(Math.abs(fd - want) <= 1e-4 * Math.max(1, Math.abs(want)))) { good = false; detail = `x=${x.toFixed(4)} f=${want} dF/dx=${fd}`; break; }
  }
  ok(good && tested > 0, `integral ${src}: ${detail || (tested ? '' : 'no test points')}  [result: ${res.resultTex}]`);
  ok(res.steps.length === 1 && res.steps[0].lhsTex, `integral ${src}: has a step tree`);
}

// exact forms
const INT_EXACT = [
  ['x^2', '\\frac{x^{3}}{3}'], ['1/x', '\\ln\\left|x\\right|'], ['e^x', 'e^{x}'], ['sin x', '-\\cos x'], ['7', '7x'],
  ['x e^x', 'xe^{x} - e^{x}'], ['ln x', 'x\\ln x - x'], ['1/(x^2+1)', '\\arctan x'], ['tan x', '\\ln\\left|\\sec x\\right|'],
  ['3x^2 - 4x + 1', 'x^{3} - 2x^{2} + x'], ['e^(3x)', '\\frac{e^{3x}}{3}'], ['x cos(x^2)', '\\frac{\\sin\\left(x^{2}\\right)}{2}'],
];
for (const [src, want] of INT_EXACT) {
  let got;
  try { got = Calc.integrate(Calc.parse(src), 'x').resultTex; } catch (e) { got = 'ERR ' + e.message; }
  ok(got === want, `integral exact ${src}: want ${want}  got ${got}`);
}

// techniques
const INT_RULES = [
  ['x^2', ['intPower']], ['x e^x', ['byParts']], ['x cos(x^2)', ['uSub']], ['(2x+3)/(x^2+3x+2)', ['intLogDeriv']],
  ['1/(x^2(x+1))', ['partialFrac']], ['(x^3+1)/(x^2+1)', ['polyDiv']], ['e^x sin x', ['byParts', 'cyclicParts']],
  ['sin^3 x', ['trigPowers']], ['cos^2 x', ['halfAngle']], ['sec^3 x', ['reduction']], ['sin(3x)cos(2x)', ['productToSum']],
  ['sqrt(1-x^2)', ['trigSub']], ['1/(x^2+2x+5)', ['completeSquare']], ['sin(2x)', ['intLinearSub']], ['1/(1+cos x)', ['weierstrass']],
  ['3x^2 - 4x + 1', ['intSum', 'intConstMult']], ['(x+2)/(x^2+2x+5)', ['linOverQuad']],
];
for (const [src, want] of INT_RULES) {
  let got = [];
  try { got = Calc.integrate(Calc.parse(src), 'x').rules; } catch (e) { got = ['ERR ' + e.message]; }
  ok(want.every((r) => got.includes(r)), `integral rules ${src}: want ${want} got ${got}`);
}

// another variable of integration
{
  const r = Calc.integrate(Calc.parse('t sin t'), 't');
  ok(r.resultTex === '\\sin t - t\\cos t', 'integral in t: ' + r.resultTex);
  ok(r.steps[0].lhsTex.endsWith('\\,dt'), 'integral in t ends with dt');
}

// no elementary antiderivative
for (const src of ['e^(x^2)', 'e^(-x^2)', 'sin(x^2)', 'sin x / x', 'e^x/x', '1/ln x', 'x^x', 'sqrt(1+x^3)']) {
  let flag = null;
  try { Calc.integrate(Calc.parse(src), 'x'); flag = 'solved?!'; } catch (e) { flag = e instanceof Calc.IntegrationError && e.nonElementary; }
  ok(flag === true, `non-elementary ${src}: got ${flag}`);
}

// rule database integrity
if (Calc.RULES) {
  const ids = new Set(Calc.RULES.map((r) => r.id));
  for (const r of Calc.RULES) {
    for (const p of r.provedFrom) ok(ids.has(p), `rule ${r.id} cites unknown ${p}`);
    ok(r.proof && r.proof.length > 0, `rule ${r.id} has a proof`);
  }
  // every rule id the engine emits exists
  const emitted = new Set();
  for (const [src] of NUMERIC) Calc.derive(Calc.parse(src), 'x', 1).rules.forEach((r) => emitted.add(r));
  for (const [src] of INTEGRALS) { try { Calc.integrate(Calc.parse(src), 'x').rules.forEach((r) => emitted.add(r)); } catch (e) { /* reported above */ } }
  // every rule's example parses, and integration examples actually integrate
  for (const r of Calc.RULES) {
    if (!r.example) continue;
    let okEx = true;
    try {
      const t = Calc.parse(r.example);
      if (Calc.INT_CATS.has(r.cat)) Calc.integrate(t, 'x'); else Calc.derive(t, 'x', 1);
    } catch (e) { okEx = false; }
    ok(okEx, `rule ${r.id} example "${r.example}" works`);
  }
  for (const r of emitted) ok(ids.has(r), `engine emits unknown rule ${r}`);
  // acyclic
  const byId = Object.fromEntries(Calc.RULES.map((r) => [r.id, r]));
  const state = {};
  const visit = (id, trail) => {
    if (state[id] === 2) return;
    if (state[id] === 1) { ok(false, 'cycle: ' + trail.concat(id).join(' → ')); return; }
    state[id] = 1;
    (byId[id] ? byId[id].provedFrom : []).forEach((p) => visit(p, trail.concat(id)));
    state[id] = 2;
  };
  Calc.RULES.forEach((r) => visit(r.id, []));
}

// math field: text → model → text keeps the meaning
if (Calc.MathField) {
  const { Field, fromText, serialize } = Calc.MathField;
  for (const [src, [lo, hi]] of NUMERIC) {
    let back, t1, t2;
    try { back = serialize(fromText(src)).text; t1 = Calc.parse(src); t2 = Calc.parse(back); }
    catch (e) { ok(false, `mathfield round trip ${src}: ${e.message} (got "${back}")`); continue; }
    let good = true, detail = '';
    for (let i = 0; i < 4; i++) {
      const x = rand(lo, hi), env = Object.assign({ x }, ENV_CONST);
      const a = Calc.evaluate(t1, env), b = Calc.evaluate(t2, env);
      if (!isFinite(a)) continue;
      if (!(Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(a)))) { good = false; detail = `x=${x} ${a} vs ${b}`; break; }
    }
    ok(good, `mathfield round trip ${src} → ${back}: ${detail}`);
    // and the serialised text is stable
    ok(serialize(fromText(back)).text === back, `mathfield stable ${src}: ${back} → ${serialize(fromText(back)).text}`);
  }
  // keystrokes (multi-letter entries are Field methods)
  const type = (keys) => {
    const f = new Field();
    for (const k of keys) { if (k.length > 1) f[k](); else f.type(k); }
    return f.getText();
  };
  const KEYS = [
    [['x', '^', '2', 'right', '/', '3'], '(x^2)/3'],
    [['1', '/', 'x', '^', '2', ' ', '+', '1'], '1/(x^2 + 1)'],
    [[...'x^2 sin x'], 'x^2 sin x'],
    [[...'arcs', 'acceptGhost', 'x'], 'arcsin(x)'],
    [[...'co', 'acceptGhost', '2', 'x'], 'cos(2x)'],
    [[...'sq', 'acceptGhost', 'x'], 'sqrt(x)'],
    [[...'sqrtx', 'right', '+', '1'], 'sqrt(x) + 1'],
    [[...'cbrtx'], 'cbrt(x)'],
    [[...'abs', 'x'], '|x|'],
    [[...'|x|+1'], '|x| + 1'],
    [[...'(1/x)+1'], '(1/x) + 1'],
    [[...'x+1)^2'], '(x + 1)^2'],
    [[...'log_2', 'right', 'x'], 'log_2 x'],
    [[...'2pi x'], '2pi x'],
    [[...'x**3'], 'x^3'],
    [[...'x²+x³'], 'x^2 + x^3'],
    [['x', '/', 'backspace'], 'x'],
    [[...'x/y', 'left', 'backspace'], 'xy'],          // backspace at the start of a slot unwraps
    [[...'x/y', 'left', 'left', 'backspace'], '()/y'], // ← from the denominator goes to the numerator
    [[...'x^2', 'backspace', 'backspace'], 'x'],
    [[...'sin(x)', 'backspace', 'backspace', 'backspace'], 'sin'], // enter, delete x, delete ()
    [[...'x/y', 'up', 'z'], '(xz)/y'],
    [[...'x/y', 'up', 'down', 'z'], 'x/(yz)'],
    [[...'x+1', 'selectAll', 'backspace', 'y'], 'y'],
    [[...'x', 'home', '2'], '2x'],
  ];
  for (const [keys, want] of KEYS) {
    let got;
    try { got = type(keys); } catch (e) { got = 'ERR ' + e.message; }
    ok(got === want, `mathfield keys ${keys.join(' ')}: want ${want} got ${got}`);
  }
  // ghost text suggestions
  const ghost = (s) => { const f = new Field(); f.typeString(s); const g = f.ghost(); return g ? g.name : null; };
  ok(ghost('arcs') === 'arcsin', 'ghost arcs → arcsin');
  ok(ghost('x') === null, 'no ghost for a single letter');
  ok(ghost('sin') === null, 'no ghost for a complete name');
  ok(ghost('2ta') === 'tan', 'ghost after a number');
  // parse error positions map back to the atom at fault
  {
    const f = new Field(); f.setText('x^2 + ');
    let pos = null; try { Calc.parse(f.getText()); } catch (e) { pos = e.pos; }
    ok(f.errorAt(pos) === 'end', 'error at end of "x^2 +" maps to end');
    const g = new Field(); g.typeString('x^'); // empty exponent
    try { Calc.parse(g.getText()); } catch (e) { pos = e.pos; }
    const at = g.errorAt(pos);
    ok(at && at.k === 'sup', `empty exponent error maps to the exponent (got ${at && at.k})`);
    const h = new Field(); h.setText('2 $ x');
    try { Calc.parse(h.getText()); } catch (e) { pos = e.pos; }
    const at2 = h.errorAt(pos);
    ok(at2 && at2.c === '$', `bad character maps to that character (got ${at2 && at2.c})`);
  }
}

console.log(`${pass} passed, ${fail} failed`);
failures.forEach((f) => console.log('  ✗ ' + f));
process.exit(fail ? 1 : 0);
