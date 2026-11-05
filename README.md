# Calculus Solver

A static, dependency-free website that differentiates and integrates single-variable functions **step by step**, including definite and improper integrals.
Every step names the rule it uses. Clicking a rule shows:
- the rule's statement
- a proof (back to the limit definition)
- a map of which rules it is proved from and which rules it proves

## Features
- **Derivatives**: you type something like `x^2 sin x`, `x^x`, `ln(sec x + tan x)` or `arcsin(2x)` and get a collapsible step tree. The tree shows:
  - the rule's formula
  - the substitution (u = …)
  - the set-up with d/dx placeholders
  - each sub-derivative
  - the combined expression and the simplified result
- **Indefinite integrals**: type an integrand such as `x e^x`, `1/(x^2(x+1))`, `sin^3 x` or `sqrt(1-x^2)` and get a step tree ending in `+ C`. The techniques, tried in this order:
  - constant, sum and constant-multiple rules
  - a table of common integrals (powers, `1/x`, exponentials, all six trig and hyperbolic functions, `|x|`, and the arctan, arcsin, arcsec and logarithmic forms), with a linear inner argument `ax + b`
  - `g'/g → ln|g|`
  - rational functions: long division, partial fractions (repeated and quadratic factors), linear over quadratic, completing the square
  - trig integrals: odd powers, half-angle, `tanᵐ secⁿ`, reduction formulas, product-to-sum
  - u-substitution (including back-solving `x = (u − b)/a`)
  - trigonometric substitution with back-substitution from the reference triangle
  - integration by parts using LIATE, repeated and cyclic
  - the tangent half-angle (Weierstrass) substitution

  Every candidate answer is differentiated numerically and compared with the integrand before it is shown. The result card also shows the symbolic derivative as a check, with a button that opens it in the derivative tab. Integrands with no elementary antiderivative (`e^(x^2)`, `sin x / x`, `1/ln x`, `x^x` and others) are recognized and named.
- **Definite and improper integrals**: fill in the limits above and below the ∫ (e.g. `0` and `pi/2`; `inf`, `-inf` or `∞` for improper integrals). Leave both empty for an antiderivative. The routes, tried in this order:
  - odd symmetry on [−a, a], which gives 0 even without an antiderivative
  - the Fundamental Theorem of Calculus, using the antiderivative from the indefinite integrator. The interval is split where the integrand blows up or where the antiderivative formula jumps (e.g. tangent half-angle answers at x = π). ∞ limits and singular endpoints become limits of F, which are found numerically and then named exactly when recognized (π/2, √π, ln 2, …). Values at nice angles are exact (sin(π/6) = 1/2, arctan 1 = π/4).
  - a table of famous definite integrals: Gaussian, Dirichlet (sin x / x), sin²x/x², Gamma (xⁿe^(−ax) = n!/aⁿ⁺¹), x/(eˣ−1) = π²/6 and ln(sin x) on [0, π/2]
  - numerical double-exponential (tanh–sinh / exp–sinh) quadrature, shown with ≈

  Divergent integrals are detected and reported (to ±∞, or no limit). Every exact answer is checked against the numerical value before it is shown. A **Riemann sums** card plots the integrand with its signed area, and draws left, right, midpoint or trapezoid strips with an n slider, the error, and a convergence table.
- **Visual math input**: the equation renders as you type, with the cursor inside the math.
  - `/` builds a stacked fraction, `^` an exponent and `_` a log base; `(` and `|` add auto-sizing brackets; `sqrt`, `cbrt` and `abs` turn into √▢, ∛▢ and |▢|.
  - Function names are colored by rule family (trig, inverse trig, exp/log, hyperbolic …), in the same colors as the rule chips and the Proof Map.
  - Ghost-text autocomplete: type `arcs` and press Tab to get arcsin(▢).
  - A parse error is underlined at the exact part of the math that caused it.
  - The **Text** button switches to a plain-text input; both modes share links.
- **Sidebar**: a "Rules used" list (in order of first use, with how many steps use each rule) and a list of examples. Hovering a rule highlights the steps that use it, and hovering a step highlights its rules. On narrow screens the sidebar moves under the result.
- **Options**: higher-order derivatives (up to 4th), a choice of variable (x, t, y, z, u, s, θ), and other letters treated as constants.
- **Rule Library**: 117 rules, each with a statement and a proof:
  - Foundations (ε–δ limits, limit laws, squeeze theorem, special limits, *e*)
  - Basic rules
  - Techniques (implicit and logarithmic differentiation, inverse function theorem)
  - Exponentials and logarithms
  - All six trig functions, inverse trig, hyperbolic and inverse hyperbolic functions
  - Roots and absolute value
  - Integration basics (antiderivatives and +C, from the Mean Value Theorem), a table of common integrals, and integration techniques. Each is proved from the derivative rule it reverses.
  - Definite integrals: Riemann sums, the Fundamental Theorem of Calculus, properties and symmetry, improper integrals, numerical integration and the famous results above
- **Proof Map**: a pan-and-zoom DAG of how every rule is proved from the others, tracing back to the definition of a limit.
- **Shareable links**: links such as `#d=sin(x^2)`, `#tab=integrate&i=x%20e%5Ex`, `#tab=integrate&i=x%5E2&lo=0&hi=1`, `#rule=byParts` and `#tab=map` open the exact view.
- **Offline**: works offline and straight from `file://`. KaTeX is vendored in `vendor/katex/` and nothing else is loaded.

## Project layout
```
index.html          page shell
css/style.css       styles (light/dark)
js/ast.js           expression nodes, exact rationals, evaluation, LaTeX printer
js/parser.js        tokenizer + parser (implicit multiplication, sin^2 x, |x|, log_b …)
js/mathfield.js     WYSIWYG, color-coded equation editor (serializes to parser syntax)
js/simplify.js      canonical simplifier + presentation pass
js/derive.js        step-tracing differentiator
js/integrate.js     step-tracing integrator (strategy search, polynomial tools, answer checking)
js/definite.js      definite & improper integrals (FTC with splitting and limits, symmetry, known results, quadrature)
js/rules.js         rule database: statements, proofs, provedFrom graph
js/proofmap.js      DAG layout + SVG rendering
js/app.js           UI wiring
tests/run.js        Node test suite
vendor/katex/       KaTeX 0.16.11 (MIT)
```

## Run locally
Open `index.html` in a browser, or serve the folder:
```sh
python3 -m http.server 8000   # then visit http://localhost:8000
```

## Tests
```sh
node tests/run.js
```
The suite checks:
- every derivative against a numeric finite difference at random points (~100 functions, plus 2nd derivatives)
- every antiderivative (~120 integrands): its numeric derivative must equal the integrand
- exact integral forms, the techniques each integral uses, and detection of non-elementary integrals
- definite integrals (~50): values, exact forms, the method used, improper and divergent cases, and agreement with Simpson's rule
- exact output forms
- rule tagging
- the parser
- the math field: text → editor → text round trips, keystroke editing, error positions
- that the rule graph has no broken links and no cycles, and that every rule's example works

## Deploy to GitHub Pages
1. Push this folder to a GitHub repository, with `index.html` at the repo root.
2. In the repo, go to **Settings → Pages → Build and deployment** and choose **Deploy from a branch**.
3. Select `main` and `/ (root)`, then save. The site appears at `https://<user>.github.io/<repo>/`.

There is no build step.
