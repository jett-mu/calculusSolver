/* mathfield.js — a WYSIWYG, colour-coded math input.
 *
 * Model: a Row is { a: [atoms], par: atom|null }. Atoms:
 *   { k:'ch', c }                      one character (digit, letter, operator, Greek glyph, space)
 *   { k:'frac', num: Row, den: Row }   stacked fraction
 *   { k:'sup',  exp: Row }             exponent of the atom before it
 *   { k:'sub',  base: Row }            log base (only after "log")
 *   { k:'root', arg: Row, n: 2|3 }     square / cube root
 *   { k:'grp',  inner: Row, kind }     brackets: kind '(' or '|'
 * Function names stay as plain letters; they are recognised (and coloured) by the same greedy
 * longest-match the tokenizer uses, so "sin" → "sinh" just re-renders.
 *
 * The model serialises to the plain-text syntax parser.js reads, so the parser stays the
 * single source of truth and #d= links stay readable. The model half is DOM-free (tested in Node);
 * mount() adds rendering and input handling in the browser. */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});

  /* ---------------- vocabulary ---------------- */
  const GREEK = { pi: 'π', theta: 'θ', alpha: 'α', beta: 'β', phi: 'φ', omega: 'ω' };
  const GREEK_NAME = {};
  Object.keys(GREEK).forEach((k) => { GREEK_NAME[GREEK[k]] = k; });

  const CAT = {};
  const setCat = (names, c) => names.split(' ').forEach((n) => { CAT[n] = c; });
  setCat('sin cos tan cot sec csc', 'trig');
  setCat('asin acos atan acot asec acsc', 'invtrig');
  setCat('sinh cosh tanh coth sech csch', 'hyp');
  setCat('asinh acosh atanh acoth asech acsch', 'invhyp');
  setCat('ln log exp', 'explog');
  setCat('sqrt cbrt abs', 'algebraic');

  const DISPLAY_NAME = {
    asin: 'arcsin', acos: 'arccos', atan: 'arctan', acot: 'arccot', asec: 'arcsec', acsc: 'arccsc',
    asinh: 'arsinh', acosh: 'arcosh', atanh: 'artanh', acoth: 'arcoth', asech: 'arsech', acsch: 'arcsch',
  };
  const INVERTIBLE = new Set('sin cos tan cot sec csc sinh cosh tanh coth sech csch'.split(' '));
  // autocomplete candidates, most common first (so "arcs" → arcsin, "se" → sec)
  const COMPLETIONS = ('sin cos tan sec csc cot sinh cosh tanh sech csch coth arcsin arccos arctan arcsec arccsc arccot ' +
    'arsinh arcosh artanh arsech arcsch arcoth ln log exp sqrt cbrt abs').split(' ');
  const STRUCTURAL = new Set(['sqrt', 'cbrt', 'abs']);

  let WORDS = null;
  function words() {
    if (!WORDS) WORDS = Object.keys(Calc.FUNC_ALIASES || {}).concat(Object.keys(GREEK)).sort((a, b) => b.length - a.length);
    return WORDS;
  }
  // split a run of letters exactly the way parser.js does
  function tokenizeRun(run) {
    const out = [];
    const W = words(), F = Calc.FUNC_ALIASES || {};
    let j = 0;
    while (j < run.length) {
      const rest = run.slice(j).toLowerCase();
      const w = W.find((x) => rest.startsWith(x));
      if (w) { out.push({ w, start: j, end: j + w.length, fn: F[w] || null, greek: GREEK[w] ? w : null }); j += w.length; }
      else { out.push({ w: run[j], start: j, end: j + 1, fn: null, greek: null }); j++; }
    }
    return out;
  }

  /* ---------------- model ---------------- */
  const isCh = (a, re) => !!a && a.k === 'ch' && re.test(a.c);
  const isLetter = (a) => isCh(a, /^[A-Za-z]$/);
  const isDigit = (a) => isCh(a, /^[0-9.]$/);
  const isSpace = (a) => !!a && a.k === 'ch' && a.c === ' ';
  const isGreek = (a) => !!a && a.k === 'ch' && !!GREEK_NAME[a.c];
  const OPS = new Set(['+', '-', '*', ',', '=']);

  function put(r, i, atoms) { atoms.forEach((a) => { a.par = r; }); r.a.splice(i, 0, ...atoms); }
  function mkRow(atoms, par) { const r = { a: [], par: par || null }; if (atoms && atoms.length) put(r, 0, atoms); return r; }
  const ch = (c) => ({ k: 'ch', c });
  function frac(n, d) { const a = { k: 'frac' }; a.num = mkRow(n, a); a.den = mkRow(d, a); return a; }
  function sup(e) { const a = { k: 'sup' }; a.exp = mkRow(e, a); return a; }
  function sub(b) { const a = { k: 'sub' }; a.base = mkRow(b, a); return a; }
  function rt(x, n) { const a = { k: 'root', n: n || 2 }; a.arg = mkRow(x, a); return a; }
  function grp(x, kind) { const a = { k: 'grp', kind: kind || '(' }; a.inner = mkRow(x, a); return a; }
  function kids(a) {
    switch (a.k) {
      case 'frac': return [a.num, a.den];
      case 'sup': return [a.exp];
      case 'sub': return [a.base];
      case 'root': return [a.arg];
      case 'grp': return [a.inner];
      default: return [];
    }
  }
  const emptyAtom = (a) => kids(a).every((r) => !r.a.length);

  // per-index info about letters: which token (function word, Greek name, single letter) they belong to
  function letterInfo(r) {
    const info = new Array(r.a.length).fill(null);
    let i = 0;
    while (i < r.a.length) {
      if (!isLetter(r.a[i])) { i++; continue; }
      let j = i;
      while (j < r.a.length && isLetter(r.a[j])) j++;
      const run = r.a.slice(i, j).map((a) => a.c).join('');
      tokenizeRun(run).forEach((t) => {
        for (let p = t.start; p < t.end; p++) info[i + p] = { tok: t, first: p === t.start, last: p === t.end - 1 };
      });
      i = j;
    }
    return info;
  }
  // is there an operand (not an operator / start of row) directly before index i?
  function operandBefore(r, i) {
    let j = i - 1;
    while (j >= 0 && isSpace(r.a[j])) j--;
    if (j < 0) return false;
    const a = r.a[j];
    return !(a.k === 'ch' && OPS.has(a.c));
  }

  /* ---------------- serialise: model → parser text ---------------- */
  function serialize(rootRow) {
    let s = '';
    const map = [];
    const last = () => s[s.length - 1] || '';
    const space = () => { if (s && last() !== ' ' && last() !== '(') s += ' '; };
    const plainNum = (r) => r.a.length > 0 && r.a.every(isDigit) && r.a.some((a) => a.c !== '.');
    const simple = (r) => plainNum(r) || (r.a.length === 1 && (isLetter(r.a[0]) || isGreek(r.a[0]) || (r.a[0].k === 'grp' && r.a[0].kind === '(')));
    const hasBar = (r) => r.a.some((a) => (a.k === 'grp' && a.kind === '|') || kids(a).some(hasBar));
    const word = (a) => isLetter(a) || isDigit(a) || isGreek(a);
    function slot(r) { const sm = simple(r); if (!sm) s += '('; row(r); if (!sm) s += ')'; }

    function row(r) {
      const info = letterInfo(r);
      r.a.forEach((a, i) => {
        const next = r.a[i + 1];
        const start = s.length;
        if (a.k === 'ch') {
          const c = a.c;
          if (c === ' ') { space(); return; }
          if (/[A-Za-z]/.test(c)) {
            const t = info[i];
            if (t.first && t.tok.fn && /[A-Za-z0-9.)]/.test(last())) space();
            s += c;
            if (t.last && t.tok.fn && word(next)) s += ' ';
          } else if (GREEK_NAME[c]) {
            if (/[A-Za-z]/.test(last())) space();
            s += GREEK_NAME[c];
            if (isLetter(next)) s += ' ';
          } else if (c === '+' || c === '-') {
            if (operandBefore(r, i)) { space(); s += c + ' '; } else s += c;
          } else if (c === '*') s += '*';
          else if (c === ',') s += ', ';
          else s += c;
        } else if (a.k === 'frac') {
          const wrap = operandBefore(r, i) || (next && next.k === 'sup');
          if (wrap) s += '(';
          slot(a.num); s += '/'; slot(a.den);
          if (wrap) s += ')';
          else if (simple(a.den) && word(next)) s += ' ';
        } else if (a.k === 'sup' || a.k === 'sub') {
          s += a.k === 'sup' ? '^' : '_';
          slot(kids(a)[0]);
          if (word(next)) s += ' ';
        } else if (a.k === 'root') {
          if (/[A-Za-z0-9.)]/.test(last())) space();
          s += a.n === 3 ? 'cbrt(' : 'sqrt(';
          row(a.arg); s += ')';
        } else if (a.k === 'grp') {
          if (a.kind === '|' && hasBar(a.inner)) {
            if (/[A-Za-z0-9.)]/.test(last())) space();
            s += 'abs('; row(a.inner); s += ')';
          } else {
            s += a.kind === '|' ? '|' : '(';
            row(a.inner);
            s += a.kind === '|' ? '|' : ')';
          }
        }
        map.push({ atom: a, start, end: s.length });
      });
    }
    row(rootRow);
    return { text: s.trimEnd(), map };
  }

  /* ---------------- text → model (through the real parser) ---------------- */
  function fromText(str) {
    str = String(str == null ? '' : str);
    if (!str.trim()) return mkRow();
    let ast;
    try { ast = Calc.parse(str); } catch (e) {
      // keep unparsable input editable, character by character
      return mkRow(Array.from(str.replace(/\s+/g, ' ').trim()).map(ch));
    }
    const r = mkRow();
    conv(ast, r);
    return r;
  }
  function join(r, atoms) {
    if (!atoms.length) return;
    const l = r.a[r.a.length - 1];
    if (isLetter(l) && isLetter(atoms[0])) put(r, r.a.length, [ch(' ')]);
    put(r, r.a.length, atoms);
  }
  function atomsOf(node) { const t = mkRow(); conv(node, t); return t.a.slice(); }
  function numStr(n) {
    if (n.f) return String(n.n);
    if (n.d === 1) return String(n.n);
    let d = n.d;
    while (d % 2 === 0) d /= 2;
    while (d % 5 === 0) d /= 5;
    return d === 1 ? String(n.n / n.d) : null;
  }
  const isNegNum = (n) => n.type === 'num' && n.n < 0;
  const wrapped = (node) => grp(atomsOf(node), '(');

  function conv(n, r) {
    switch (n.type) {
      case 'num': {
        if (n.n < 0) { join(r, [ch('-')]); conv(Object.assign({}, n, { n: -n.n }), r); return; }
        const s = numStr(n);
        if (s === null) join(r, [frac(Array.from(String(n.n)).map(ch), Array.from(String(n.d)).map(ch))]);
        else join(r, Array.from(s).map(ch));
        return;
      }
      case 'const': join(r, [ch(n.name === 'pi' ? 'π' : 'e')]); return;
      case 'var': join(r, GREEK[n.name] ? [ch(GREEK[n.name])] : Array.from(n.name).map(ch)); return;
      case 'add':
        n.terms.forEach((t, i) => {
          if (i === 0) { conv(t, r); return; }
          if (t.type === 'neg') { join(r, [ch('-')]); join(r, t.arg.type === 'add' ? [wrapped(t.arg)] : atomsOf(t.arg)); }
          else if (isNegNum(t)) { join(r, [ch('-')]); conv(Object.assign({}, t, { n: -t.n }), r); }
          else { join(r, [ch('+')]); conv(t, r); }
        });
        return;
      case 'neg':
        join(r, [ch('-')]);
        join(r, n.arg.type === 'add' ? [wrapped(n.arg)] : atomsOf(n.arg));
        return;
      case 'mul':
        n.factors.forEach((f, k) => {
          const wrap = f.type === 'add' || (k > 0 && (f.type === 'neg' || isNegNum(f)));
          const atoms = wrap ? [wrapped(f)] : atomsOf(f);
          if (k > 0 && isDigit(atoms[0])) join(r, [ch('*')]);
          join(r, atoms);
        });
        return;
      case 'div': join(r, [frac(atomsOf(n.num), atomsOf(n.den))]); return;
      case 'pow': {
        const b = n.base, e = n.exp;
        const expAtoms = atomsOf(e);
        if (b.type === 'func' && !STRUCTURAL.has(b.name)) {
          const minusOne = e.type === 'num' && e.n === -1 && e.d === 1;
          if (!(minusOne && INVERTIBLE.has(b.name))) { convFunc(b, r, expAtoms); return; }
        }
        const wrap = b.type === 'add' || b.type === 'neg' || b.type === 'mul' || b.type === 'pow' || isNegNum(b);
        join(r, wrap ? [wrapped(b)] : atomsOf(b));
        put(r, r.a.length, [sup(expAtoms)]);
        return;
      }
      case 'func': convFunc(n, r, null); return;
      default: join(r, Array.from(Calc.str ? Calc.str(n) : '?').map(ch));
    }
  }
  function convFunc(n, r, powAtoms) {
    const arg = atomsOf(n.arg);
    if (n.name === 'sqrt' || n.name === 'cbrt') join(r, [rt(arg, n.name === 'cbrt' ? 3 : 2)]);
    else if (n.name === 'abs') join(r, [grp(arg, '|')]);
    else {
      join(r, Array.from(DISPLAY_NAME[n.name] || n.name).map(ch));
      if (n.base) put(r, r.a.length, [sub(atomsOf(n.base))]);
      if (powAtoms) put(r, r.a.length, [sup(powAtoms)]);
      put(r, r.a.length, [grp(arg, '(')]);
      return;
    }
    if (powAtoms) put(r, r.a.length, [sup(powAtoms)]);
  }

  /* ---------------- editor (DOM-free) ---------------- */
  const ALIAS = { '[': '(', '{': '(', ']': ')', '}': ')', '−': '-', '–': '-', '×': '*', '⋅': '*', '·': '*', '÷': '/' };

  class Field {
    constructor(text) { this.clear(); if (text) this.setText(text); }
    clear() { this.root = mkRow(); this.cur = { row: this.root, i: 0 }; this.all = false; }
    setText(s) { this.root = fromText(s); this.cur = { row: this.root, i: this.root.a.length }; this.all = false; }
    getText() { return serialize(this.root).text; }
    isEmpty() { return !this.root.a.length; }
    selectAll() { if (!this.isEmpty()) this.all = true; }
    atRowEnd() { return this.cur.i === this.cur.row.a.length; }

    insertText(s) {
      if (this.all || this.isEmpty()) { this.setText(s); return; }
      const atoms = fromText(s).a.slice();
      put(this.cur.row, this.cur.i, atoms);
      this.cur.i += atoms.length;
    }
    typeString(s) { for (const c of String(s).replace(/\*\*/g, '^')) this.type(c); }

    type(c) {
      if (this.all) this.clear();
      c = ALIAS[c] || c;
      const r = this.cur.row, i = this.cur.i;
      switch (c) {
        case '/': return this.makeFrac();
        case '^': return this.makeSup();
        case '_': return this.makeSub();
        case '(': return this.makeGroup('(');
        case ')': return this.closeGroup('(');
        case '|': return this.bar();
        case '√': return this.makeRoot(2);
        case '∛': return this.makeRoot(3);
        case '²': case '³':
          put(r, i, [sup([ch(c === '²' ? '2' : '3')])]); this.cur.i++; return;
        case '\n': case '\r': case '\t': return;
        case ' ': {
          // a space at the end of an exponent or log base steps back out to the baseline
          if (r.par && (r.par.k === 'sup' || r.par.k === 'sub') && i === r.a.length && r.a.length) { this.exitAfter(r.par); return; }
          if (i === 0 || isSpace(r.a[i - 1]) || isSpace(r.a[i])) return;
          break;
        }
        case '*':
          if (isCh(r.a[i - 1], /^\*$/)) { r.a.splice(i - 1, 1); this.cur.i--; return this.makeSup(); } // ** → power
          break;
        default:
      }
      if (/\s/.test(c)) return;
      put(r, i, [ch(c)]);
      this.cur.i++;
      if (/[A-Za-z]/.test(c)) this.autoConvert();
    }

    exitAfter(a) { const pr = a.par; this.cur = { row: pr, i: pr.a.indexOf(a) + 1 }; }
    runBefore() {
      const r = this.cur.row, i = this.cur.i;
      let j = i;
      while (j > 0 && isLetter(r.a[j - 1])) j--;
      return { start: j, text: r.a.slice(j, i).map((a) => a.c).join('') };
    }
    lastToken() {
      const rb = this.runBefore();
      if (!rb.text) return null;
      const toks = tokenizeRun(rb.text);
      const t = toks[toks.length - 1];
      return { t, toks, rb };
    }
    // "sqrt" → √▢, "cbrt" → ∛▢, "abs" → |▢|, "pi"/"theta"/… → Greek glyph
    autoConvert() {
      const r = this.cur.row;
      if (isLetter(r.a[this.cur.i])) return false;
      const lt = this.lastToken();
      if (!lt) return false;
      const { t, rb } = lt;
      const w = t.w.toLowerCase();
      if (t.end !== rb.text.length || w.length < 2) return false;
      let atom = null, into = null;
      if (w === 'sqrt' || w === 'cbrt') { atom = rt([], w === 'cbrt' ? 3 : 2); into = atom.arg; }
      else if (w === 'abs') { atom = grp([], '|'); into = atom.inner; }
      else if (GREEK[w]) atom = ch(GREEK[w]);
      else return false;
      const at = rb.start + t.start;
      r.a.splice(at, w.length);
      put(r, at, [atom]);
      this.cur = into ? { row: into, i: 0 } : { row: r, i: at + 1 };
      return true;
    }

    makeFrac() {
      const r = this.cur.row, i = this.cur.i;
      let j = i;
      while (j > 0 && !isCh(r.a[j - 1], /^[+\-,=]$/)) j--;
      while (j < i && isSpace(r.a[j])) j++;
      const numAtoms = r.a.splice(j, i - j);
      const f = frac(numAtoms, []);
      put(r, j, [f]);
      this.cur = numAtoms.length ? { row: f.den, i: 0 } : { row: f.num, i: 0 };
    }
    makeSup() {
      const r = this.cur.row, i = this.cur.i;
      const p = r.a[i - 1], n = r.a[i];
      if (p && p.k === 'sup') { this.cur = { row: p.exp, i: p.exp.a.length }; return; }
      if (n && n.k === 'sup') { this.cur = { row: n.exp, i: 0 }; return; }
      const s = sup([]);
      put(r, i, [s]);
      this.cur = { row: s.exp, i: 0 };
    }
    makeSub() {
      const r = this.cur.row, i = this.cur.i;
      if (r.a[i - 1] && r.a[i - 1].k === 'sub') { const b = r.a[i - 1].base; this.cur = { row: b, i: b.a.length }; return; }
      const lt = this.lastToken();
      if (!lt || lt.t.w.toLowerCase() !== 'log' || lt.t.end !== lt.rb.text.length) return;
      const s = sub([]);
      put(r, i, [s]);
      this.cur = { row: s.base, i: 0 };
    }
    makeGroup(kind) {
      const g = grp([], kind);
      put(this.cur.row, this.cur.i, [g]);
      this.cur = { row: g.inner, i: 0 };
    }
    makeRoot(n) {
      const a = rt([], n);
      put(this.cur.row, this.cur.i, [a]);
      this.cur = { row: a.arg, i: 0 };
    }
    openGroup(kind) {
      for (let r = this.cur.row; r.par; r = r.par.par) if (r.par.k === 'grp' && r.par.kind === kind) return r.par;
      return null;
    }
    // close the nearest open bracket of this kind, carrying anything after the cursor out with it
    closeGroup(kind) {
      let r = this.cur.row, i = this.cur.i;
      while (r.par && !(r.par.k === 'grp' && r.par.kind === kind)) { const a = r.par; r = a.par; i = r.a.indexOf(a) + 1; }
      if (r.par) {
        const g = r.par;
        const tail = r.a.splice(i);
        const pr = g.par, idx = pr.a.indexOf(g);
        put(pr, idx + 1, tail);
        this.cur = { row: pr, i: idx + 1 };
        return;
      }
      // no open bracket: wrap everything before the cursor in this row
      const cr = this.cur.row;
      if (kind === '(' && this.cur.i > 0) {
        const body = cr.a.splice(0, this.cur.i);
        put(cr, 0, [grp(body, '(')]);
        this.cur = { row: cr, i: 1 };
      }
    }
    bar() { if (this.openGroup('|')) this.closeGroup('|'); else this.makeGroup('|'); }

    /* --- movement --- */
    left() {
      if (this.all) { this.all = false; this.cur = { row: this.root, i: 0 }; return; }
      const r = this.cur.row, i = this.cur.i;
      if (i > 0) {
        const ks = kids(r.a[i - 1]);
        if (ks.length) { const k = ks[ks.length - 1]; this.cur = { row: k, i: k.a.length }; }
        else this.cur.i--;
        return;
      }
      const p = r.par;
      if (!p) return;
      const ks = kids(p), idx = ks.indexOf(r);
      if (idx > 0) { const k = ks[idx - 1]; this.cur = { row: k, i: k.a.length }; }
      else this.cur = { row: p.par, i: p.par.a.indexOf(p) };
    }
    right() {
      if (this.all) { this.all = false; this.cur = { row: this.root, i: this.root.a.length }; return; }
      const r = this.cur.row, i = this.cur.i;
      if (i < r.a.length) {
        const ks = kids(r.a[i]);
        if (ks.length) this.cur = { row: ks[0], i: 0 };
        else this.cur.i++;
        return;
      }
      const p = r.par;
      if (!p) return;
      const ks = kids(p), idx = ks.indexOf(r);
      if (idx < ks.length - 1) this.cur = { row: ks[idx + 1], i: 0 };
      else this.exitAfter(p);
    }
    up() {
      this.all = false;
      for (let r = this.cur.row; r.par; r = r.par.par) {
        const a = r.par;
        if (a.k === 'frac' && r === a.den) { this.cur = { row: a.num, i: a.num.a.length }; return; }
        if (a.k === 'sub') { this.exitAfter(a); return; }
      }
      const r = this.cur.row, i = this.cur.i, p = r.a[i - 1], n = r.a[i];
      if (p && p.k === 'sup') this.cur = { row: p.exp, i: p.exp.a.length };
      else if (n && n.k === 'sup') this.cur = { row: n.exp, i: 0 };
    }
    down() {
      this.all = false;
      for (let r = this.cur.row; r.par; r = r.par.par) {
        const a = r.par;
        if (a.k === 'frac' && r === a.num) { this.cur = { row: a.den, i: a.den.a.length }; return; }
        if (a.k === 'sup') { this.exitAfter(a); return; }
      }
      const r = this.cur.row, i = this.cur.i, p = r.a[i - 1], n = r.a[i];
      if (p && p.k === 'sub') this.cur = { row: p.base, i: p.base.a.length };
      else if (n && n.k === 'sub') this.cur = { row: n.base, i: 0 };
    }
    home() { this.all = false; this.cur = { row: this.root, i: 0 }; }
    end() { this.all = false; this.cur = { row: this.root, i: this.root.a.length }; }
    tabOut() { const r = this.cur.row; if (!r.par) return false; this.cur.i = r.a.length; this.right(); return true; }
    tabBack() { const r = this.cur.row; if (!r.par) return false; this.cur.i = 0; this.left(); return true; }

    /* --- deletion --- */
    removeAtom(a) { const pr = a.par, idx = pr.a.indexOf(a); pr.a.splice(idx, 1); this.cur = { row: pr, i: idx }; }
    // replace a structure with its contents; the cursor lands where `inside` began (or ended)
    unwrap(a, inside, atEnd) {
      const pr = a.par, idx = pr.a.indexOf(a);
      const flat = [];
      let at = 0;
      kids(a).forEach((k) => { if (k === inside) at = flat.length + (atEnd ? k.a.length : 0); flat.push(...k.a); });
      pr.a.splice(idx, 1);
      put(pr, idx, flat);
      this.cur = { row: pr, i: idx + at };
    }
    backspace() {
      if (this.all) { this.clear(); return; }
      const r = this.cur.row, i = this.cur.i;
      if (i > 0) {
        const a = r.a[i - 1];
        if (a.k === 'ch' || emptyAtom(a)) { r.a.splice(i - 1, 1); this.cur.i--; }
        else { const ks = kids(a), k = ks[ks.length - 1]; this.cur = { row: k, i: k.a.length }; }
        return;
      }
      const p = r.par;
      if (!p) return;
      if (emptyAtom(p)) this.removeAtom(p); else this.unwrap(p, r, false);
    }
    del() {
      if (this.all) { this.clear(); return; }
      const r = this.cur.row, i = this.cur.i;
      if (i < r.a.length) {
        const a = r.a[i];
        if (a.k === 'ch' || emptyAtom(a)) r.a.splice(i, 1);
        else this.cur = { row: kids(a)[0], i: 0 };
        return;
      }
      const p = r.par;
      if (!p) return;
      if (emptyAtom(p)) this.removeAtom(p); else this.unwrap(p, r, true);
    }

    /* --- autocomplete --- */
    ghost() {
      if (this.all) return null;
      const r = this.cur.row;
      if (isLetter(r.a[this.cur.i])) return null;
      const lt = this.lastToken();
      if (!lt) return null;
      const s0 = lt.rb.text.toLowerCase();
      if (s0.length < 2) return null;
      if (lt.t.fn && lt.t.end === s0.length) return null; // already a complete function name
      for (let k = Math.min(s0.length, 6); k >= 2; k--) {
        const off = s0.length - k;
        if (!lt.toks.some((x) => x.start === off)) continue;
        const s = s0.slice(off);
        const name = COMPLETIONS.find((n) => n.length > k && n.startsWith(s));
        if (name) return { rest: name.slice(k), name, structural: STRUCTURAL.has(name) };
      }
      return null;
    }
    acceptGhost() {
      const g = this.ghost();
      if (!g) return false;
      for (const c of g.rest) { put(this.cur.row, this.cur.i, [ch(c)]); this.cur.i++; }
      if (this.autoConvert()) return true;
      const n = this.cur.row.a[this.cur.i];
      if (n && n.k === 'grp' && n.kind === '(') this.cur = { row: n.inner, i: 0 };
      else this.makeGroup('(');
      return true;
    }

    // which atom does a ParseError position in getText() point at? ('end' = past the last atom)
    errorAt(pos) {
      const { text, map } = serialize(this.root);
      if (typeof pos !== 'number' || pos >= text.length) return 'end';
      let best = null;
      for (const m of map) {
        if (m.start <= pos && pos < m.end && (!best || m.end - m.start < best.end - best.start)) best = m;
      }
      if (!best) for (const m of map) if (m.start >= pos && (!best || m.start < best.start)) best = m;
      return best ? best.atom : 'end';
    }
  }

  /* ---------------- browser: rendering + input ---------------- */
  const SVG_NS = 'http://www.w3.org/2000/svg';
  const PATHS = {
    open: 'M8.5,2 C1.5,28 1.5,72 8.5,98',
    close: 'M1.5,2 C8.5,28 8.5,72 1.5,98',
    bar: 'M5,2 L5,98',
    radix: 'M1,64 L5,57 L10.5,97 L20,0.8',
  };
  function svg(kind, cls) {
    const s = document.createElementNS(SVG_NS, 'svg');
    s.setAttribute('viewBox', kind === 'radix' ? '0 0 20 100' : '0 0 10 100');
    s.setAttribute('preserveAspectRatio', 'none');
    s.setAttribute('aria-hidden', 'true');
    s.setAttribute('class', cls);
    const p = document.createElementNS(SVG_NS, 'path');
    p.setAttribute('d', PATHS[kind]);
    p.setAttribute('vector-effect', 'non-scaling-stroke');
    s.appendChild(p);
    return s;
  }

  function mount(host, opts) {
    opts = opts || {};
    const f = new Field();
    const SENT = '​'; // sentinel kept in the hidden textarea so mobile backspace always fires
    host.classList.add('mf');
    host.innerHTML = '';
    const view = document.createElement('div');
    view.className = 'mf-view';
    view.setAttribute('aria-hidden', 'true');
    if (opts.placeholder) view.dataset.ph = opts.placeholder;
    const ta = document.createElement('textarea');
    ta.className = 'mf-ta';
    ta.rows = 1;
    ['autocomplete', 'autocorrect', 'autocapitalize'].forEach((a) => ta.setAttribute(a, 'off'));
    ta.spellcheck = false;
    ta.setAttribute('aria-label', opts.label || 'Math input');
    host.append(view, ta);

    let focused = false, err = null, lastText = '', composing = false;
    const span = (cls, text) => { const e = document.createElement('span'); e.className = cls; if (text != null) e.textContent = text; return e; };
    const resetTa = () => {
      if (f.all) { ta.value = f.getText() || SENT; ta.select(); return; }
      ta.value = SENT;
      try { ta.setSelectionRange(1, 1); } catch (e) { /* not focusable yet */ }
    };

    function render() {
      const g = focused ? f.ghost() : null;
      view.textContent = '';
      view.appendChild(buildRow(f.root, g));
      host.classList.toggle('mf-focus', focused);
      host.classList.toggle('mf-all', f.all);
      host.classList.toggle('mf-blank', f.isEmpty());
      host.classList.toggle('mf-err-end', err === 'end');
      const c = view.querySelector('.mf-cursor');
      if (c && focused) {
        // keep the cursor in view when the expression is wider than the field
        const hb = host.getBoundingClientRect(), cb = c.getBoundingClientRect();
        if (cb.right > hb.right - 24) host.scrollLeft += cb.right - hb.right + 40;
        else if (cb.left < hb.left + 12) host.scrollLeft -= hb.left - cb.left + 40;
      }
    }
    function cursorEls(row, g) {
      const out = [span('mf-cursor')];
      if (g) {
        const gh = span('mf-ghost');
        gh.appendChild(span('mf-ghost-txt', g.rest + (g.structural ? '' : '(')));
        if (!g.structural) { gh.appendChild(span('mf-ph')); gh.appendChild(span('mf-ghost-txt', ')')); }
        gh.appendChild(span('mf-key', 'tab'));
        out.push(gh);
      }
      return out;
    }
    function buildRow(r, g) {
      const el = span('mf-row');
      el._row = r;
      const here = focused && !f.all && f.cur.row === r;
      if (here && r !== f.root) el.classList.add('mf-here');
      const info = letterInfo(r);
      if (!r.a.length) {
        el.classList.add('mf-empty');
        if (here) el.append(...cursorEls(r, g));
        if (r !== f.root) el.appendChild(span('mf-ph'));
        return el;
      }
      r.a.forEach((a, i) => {
        if (here && f.cur.i === i) el.append(...cursorEls(r, g));
        el.appendChild(buildAtom(a, r, i, info, g));
      });
      if (here && f.cur.i === r.a.length) el.append(...cursorEls(r, g));
      return el;
    }
    // category of the function a bracket group is the argument of (sin(…) → trig)
    function argCat(r, i, info) {
      let j = i - 1;
      while (j >= 0 && (r.a[j].k === 'sup' || r.a[j].k === 'sub')) j--;
      const t = info[j];
      return t && t.last && t.tok.fn ? CAT[t.tok.fn] : null;
    }
    function buildAtom(a, r, i, info, g) {
      let el;
      const next = r.a[i + 1];
      if (a.k === 'ch') {
        const c = a.c;
        if (/[A-Za-z]/.test(c)) {
          const t = info[i];
          if (t.tok.fn) {
            el = span('mf-fn cat-' + CAT[t.tok.fn], c);
            if (t.first) el.classList.add('mf-fn-s');
            if (t.last) {
              el.classList.add('mf-fn-e');
              if (next && !(next.k === 'grp' || next.k === 'sup' || next.k === 'sub' || isSpace(next))) el.classList.add('mf-gap');
            }
          } else {
            el = span('mf-var', c);
            if (c === 'e' && !t.tok.greek && next && next.k === 'sup') el.classList.add('mf-e', 'cat-explog');
          }
        } else if (/[0-9.]/.test(c)) el = span('mf-num', c);
        else if (GREEK_NAME[c]) el = span('mf-var', c);
        else if (c === '+' || c === '-') el = span(operandBefore(r, i) ? 'mf-bin' : 'mf-un', c === '-' ? '−' : '+');
        else if (c === '*') el = span('mf-bin mf-dot', '·');
        else if (c === '=') el = span('mf-bin', '=');
        else if (c === ' ') el = span('mf-sp');
        else if (c === ',') el = span('mf-punct', ',');
        else el = span('mf-sym', c);
      } else if (a.k === 'frac') {
        el = span('mf-frac');
        const n = span('mf-fnum'), d = span('mf-fden');
        n.appendChild(buildRow(a.num, g));
        d.appendChild(buildRow(a.den, g));
        el.append(n, d);
      } else if (a.k === 'sup' || a.k === 'sub') {
        el = span(a.k === 'sup' ? 'mf-sup' : 'mf-sub');
        el.appendChild(buildRow(kids(a)[0], g));
      } else if (a.k === 'root') {
        el = span('mf-root cat-algebraic');
        if (a.n === 3) el.appendChild(span('mf-index', '3'));
        el.appendChild(svg('radix', 'mf-radix'));
        const body = span('mf-rad');
        body.appendChild(buildRow(a.arg, g));
        el.appendChild(body);
      } else if (a.k === 'grp') {
        const bar = a.kind === '|';
        const cat = bar ? 'algebraic' : argCat(r, i, info);
        el = span('mf-grp' + (bar ? ' mf-abs' : '') + (cat ? ' mf-arg cat-' + cat : ''));
        el.append(svg(bar ? 'bar' : 'open', 'mf-br'), buildRow(a.inner, g), svg(bar ? 'bar' : 'close', 'mf-br'));
      }
      el.classList.add('mf-a');
      el._atom = a;
      if (err && err === a) el.classList.add('mf-err');
      return el;
    }

    function changed() {
      err = null;
      resetTa();
      render();
      const t = f.getText();
      if (t !== lastText) { lastText = t; if (opts.onChange) opts.onChange(t); }
    }

    // click → deepest row under the pointer, nearest gap between its atoms
    function place(x, y) {
      f.all = false;
      let best = null, bestArea = Infinity;
      view.querySelectorAll('.mf-row').forEach((el) => {
        const b = el.getBoundingClientRect();
        if (x >= b.left - 3 && x <= b.right + 3 && y >= b.top - 3 && y <= b.bottom + 3) {
          const ar = b.width * b.height;
          if (ar < bestArea) { bestArea = ar; best = el; }
        }
      });
      if (!best) best = view.firstChild;
      const atoms = Array.from(best.children).filter((c) => c._atom);
      let i = atoms.length;
      for (let k = 0; k < atoms.length; k++) {
        const b = atoms[k].getBoundingClientRect();
        if (x < b.left + b.width / 2) { i = k; break; }
      }
      f.cur = { row: best._row, i };
    }

    host.addEventListener('mousedown', (e) => {
      if (e.button !== 0) return;
      e.preventDefault();
      if (!focused) ta.focus({ preventScroll: true });
      place(e.clientX, e.clientY);
      changed();
    });
    host.addEventListener('touchend', (e) => {
      const t = e.changedTouches[0];
      if (!t) return;
      e.preventDefault();
      ta.focus({ preventScroll: true });
      place(t.clientX, t.clientY);
      changed();
    });
    host.addEventListener('dblclick', (e) => { e.preventDefault(); f.selectAll(); changed(); });

    ta.addEventListener('focus', () => { focused = true; resetTa(); render(); });
    ta.addEventListener('blur', () => { focused = false; f.all = false; render(); });
    ta.addEventListener('keydown', (e) => {
      if (e.isComposing || composing) return;
      const mod = e.metaKey || e.ctrlKey;
      let handled = true;
      switch (e.key) {
        case 'ArrowLeft': if (mod) f.home(); else f.left(); break;
        case 'ArrowRight': if (mod) f.end(); else if (!(f.atRowEnd() && f.acceptGhost())) f.right(); break;
        case 'ArrowUp': f.up(); break;
        case 'ArrowDown': f.down(); break;
        case 'Home': f.home(); break;
        case 'End': f.end(); break;
        case 'Backspace': f.backspace(); break;
        case 'Delete': f.del(); break;
        case 'Enter':
          e.preventDefault();
          if (opts.onEnter) opts.onEnter(f.getText());
          return;
        case 'Tab': handled = e.shiftKey ? f.tabBack() : (f.acceptGhost() || f.tabOut()); break;
        case 'Escape': if (f.all) f.all = false; else handled = false; break;
        default:
          if (mod && (e.key === 'a' || e.key === 'A')) f.selectAll();
          else handled = false;
      }
      if (handled) { e.preventDefault(); changed(); }
    });
    function sync() {
      const v = ta.value;
      if (v === SENT || (f.all && v === f.getText())) return;
      if (v.startsWith(SENT)) f.typeString(v.slice(SENT.length));
      else if (v === '') f.backspace();
      else f.typeString(v.split(SENT).join(''));
      changed();
    }
    ta.addEventListener('compositionstart', () => { composing = true; });
    ta.addEventListener('compositionend', () => { composing = false; sync(); });
    ta.addEventListener('input', () => { if (!composing) sync(); });
    ta.addEventListener('copy', (e) => { e.preventDefault(); e.clipboardData.setData('text/plain', f.getText()); });
    ta.addEventListener('cut', (e) => {
      e.preventDefault();
      e.clipboardData.setData('text/plain', f.getText());
      if (f.all) { f.clear(); changed(); }
    });
    ta.addEventListener('paste', (e) => {
      e.preventDefault();
      const t = (e.clipboardData || window.clipboardData).getData('text');
      if (t) { f.insertText(t); changed(); }
    });

    render();
    return {
      el: host,
      field: f,
      getText: () => f.getText(),
      setText(s) { f.setText(s); err = null; lastText = f.getText(); resetTa(); render(); },
      focus() { ta.focus({ preventScroll: true }); },
      markError(pos) { err = f.errorAt(pos); render(); },
      clearError() { if (err) { err = null; render(); } },
    };
  }

  Calc.MathField = { Field, serialize, fromText, tokenizeRun, mount, CAT };
})(typeof window !== 'undefined' ? window : globalThis);
