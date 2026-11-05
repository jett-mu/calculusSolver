/* app.js — UI: the two calculators (derivatives, integrals), step trees, rule drawer, library, proof map, hash routing. */
(function () {
  'use strict';
  const Calc = window.Calc;
  const $ = (s, r) => (r || document).querySelector(s);
  const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));

  /* ---------------- KaTeX helpers ---------------- */
  function k(texStr, display) {
    try {
      return katex.renderToString(texStr, { throwOnError: false, displayMode: !!display, strict: 'ignore' });
    } catch (e) { return '<code>' + esc(texStr) + '</code>'; }
  }
  function esc(s) {
    return String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  }
  // prose with $inline$, $$display$$ and **bold**
  function rich(s) {
    return s.split(/(\$\$[\s\S]+?\$\$|\$[^$]+?\$)/).map((seg) => {
      if (seg.startsWith('$$') && seg.length > 4) return k(seg.slice(2, -2), true);
      if (seg.startsWith('$') && seg.length > 2) return k(seg.slice(1, -1), false);
      return esc(seg).replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>');
    }).join('');
  }
  function proofHTML(items) {
    return items.map((it) => {
      if (it.startsWith('## ')) return '<h4>' + esc(it.slice(3)) + '</h4>';
      if (/^\$\$[\s\S]+\$\$$/.test(it.trim())) return rich(it.trim());
      return '<p>' + rich(it) + '</p>';
    }).join('');
  }
  const chip = (id) => {
    const r = Calc.RULE_BY_ID[id];
    if (!r) return '';
    return `<button class="chip cat-${r.cat}" data-rule="${r.id}" title="${esc(r.name)}: read the rule and its proof">${esc(r.name)}</button>`;
  };
  // a quiet, text-only rule label for the step tree (the sidebar lists the rules in full)
  const tag = (id) => {
    const r = Calc.RULE_BY_ID[id];
    if (!r) return '';
    return `<button class="rtag cat-${r.cat}" data-rule="${r.id}" title="${esc(r.name)}: read the rule and its proof">${esc(r.name.replace(/ Rule$/, '').replace(/ \(Integrals\)$/, ''))}</button>`;
  };
  const CHEVRON = '<svg viewBox="0 0 12 12" aria-hidden="true"><path d="M4 2l4 4-4 4" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>';
  const vtex = (v) => Calc.tex(Calc.V(v));
  function dOp(n, v) {
    return n === 1 ? '\\frac{d}{d' + vtex(v) + '}' : '\\frac{d^{' + n + '}}{d' + vtex(v) + '^{' + n + '}}';
  }

  /* ---------------- a calculator (derivative or integral) ---------------- */
  function makeSolver(cfg) {
    const ids = cfg.ids;
    const el = (name) => document.getElementById(ids[name]);
    const S = { cfg, expr: cfg.defaultExpr, v: 'x', n: 1, field: null, textMode: false, timer: null };

    const getSrc = () => (S.textMode ? el('text').value : S.field.getText());
    S.setSrc = (s) => {
      S.field.setText(s);
      el('text').value = S.textMode ? s : S.field.getText();
    };
    S.focus = () => { if (S.textMode) el('text').focus(); else S.field.focus(); };
    S.setMode = (text, focus) => {
      const cur = getSrc();
      S.textMode = text;
      if (text) el('text').value = cur; else S.field.setText(cur);
      el('field').hidden = text;
      el('text').hidden = !text;
      const b = el('mode');
      b.textContent = text ? 'Math' : 'Text';
      b.title = text ? 'Switch to the visual math editor' : 'Switch to plain-text input';
      b.setAttribute('aria-pressed', String(text));
      try { localStorage.setItem('cs-input', text ? 'text' : 'math'); } catch (e) { /* storage unavailable */ }
      if (focus) S.focus();
    };
    S.updateLabel = () => { el('label').innerHTML = k(cfg.labelTex(S)); };
    S.schedule = () => { clearTimeout(S.timer); S.timer = setTimeout(S.run, 160); };

    S.run = () => {
      const src = getSrc();
      S.expr = src;
      if (state.tab === cfg.tab) writeHash();
      const pv = el('preview'), out = el('output'), ans = el('answer');
      el('field').classList.remove('err');
      el('text').classList.remove('err');
      pv.classList.remove('err');
      if (!src.trim()) {
        pv.innerHTML = '';
        ans.innerHTML = `<div class="card hint"><h2>${cfg.emptyTitle}</h2><p>${cfg.emptyText}</p></div>`;
        out.innerHTML = '';
        S.renderRuleList(null);
        return;
      }
      let tree;
      try {
        tree = Calc.parse(src);
      } catch (e) {
        pv.classList.add('err');
        const pos = typeof e.pos === 'number' ? e.pos : src.length;
        if (S.textMode) {
          el('text').classList.add('err');
          const marked = esc(src.slice(0, pos)) + '<mark>' + (esc(src.slice(pos, pos + 1)) || '&nbsp;') + '</mark>' + esc(src.slice(pos + 1));
          pv.innerHTML = `<span>${esc(e.message)}</span> <span class="err-src">${marked}</span>`;
        } else {
          // the field itself underlines the part at fault
          el('field').classList.add('err');
          S.field.markError(pos);
          pv.innerHTML = `<span>${esc(e.message)}</span>`;
        }
        return; // keep the last good result on screen while typing
      }
      if (!S.textMode) S.field.clearError();
      const v = S.v;
      const fName = 'f(' + vtex(v) + ')';
      const consts = Array.from(Calc.freeVars(tree)).filter((x) => x !== v);
      pv.innerHTML = `<span class="lbl">Interpreted as</span> ${k(fName + ' = ' + Calc.tex(tree))}` +
        (consts.length ? `<span class="note">treating ${consts.map((c) => k(vtex(c))).join(', ')} as constant${consts.length > 1 ? 's' : ''}</span>` : '') +
        (!Calc.contains(tree, v) && !consts.length ? `<span class="note">(no ${k(vtex(v))} in this expression, so it is a constant)</span>` : '');
      let res;
      try {
        res = cfg.engine(tree, v, S.n);
      } catch (e) {
        ans.innerHTML = cfg.errorCard(e);
        out.innerHTML = '';
        S.renderRuleList(null);
        return;
      }
      S.renderResult(tree, res);
    };

    S.renderResult = (tree, res) => {
      el('answer').innerHTML = cfg.answerCard(tree, res, S);
      let html = `<div class="card steps">
        <div class="steps-head"><h2>Step by step</h2>
          <div class="actions"><button class="btn-ghost" data-act="expand">Expand all</button><button class="btn-ghost" data-act="collapse">Collapse all</button></div>
        </div>`;
      if (cfg.stepsNote) html += `<p class="steps-note">${cfg.stepsNote}</p>`;
      const names = ['', 'First derivative', 'Second derivative', 'Third derivative', 'Fourth derivative'];
      res.steps.forEach((st, i) => {
        if (res.steps.length > 1) {
          const prime = 'f' + "'".repeat(i);
          html += `<div class="order-head"><h3>${names[i + 1]}</h3>${i > 0 ? `<span class="note">differentiate ${k(prime + '(' + vtex(S.v) + ')')} again</span> <span class="step-tags">${tag('higherOrder')}</span>` : ''}</div>`;
        }
        html += '<ol class="tree">' + stepHTML(st, 0) + '</ol>';
      });
      html += '</div>';
      el('output').innerHTML = html;
      S.renderRuleList(res);
    };

    function stepHTML(st, depth) {
      const lhs = st.lhsTex || dOp(1, S.v) + '\\left[' + st.exprTex + '\\right]';
      const eq = lhs + ' = ' + st.resultTex;
      const hasBody = !!(st.formula || st.setup || st.note || st.children.length);
      const open = depth < 2 && (st.children.length > 0 || depth === 0);
      let body = '';
      if (st.formula) {
        body += `<div class="rule-line"><span class="lbl">Rule</span>${k(st.formula)}${st.where ? `<span class="where">with ${k(st.where)}</span>` : ''}</div>`;
      } else if (st.where) {
        body += `<div class="rule-line"><span class="lbl">With</span>${k(st.where)}</div>`;
      }
      if (st.note) body += `<div class="rule-line note-line"><span class="lbl">${esc(st.note.label)}</span>${k(st.note.tex)}</div>`;
      let work = '';
      if (st.setup) work += `<div class="work"><span class="eq">=</span>${k(st.setup)}</div>`;
      if (st.children.length) work += '<ol>' + st.children.map((c) => stepHTML(c, depth + 1)).join('') + '</ol>';
      if (st.back) work += `<div class="work back"><span class="lbl">${esc(st.backLabel || 'Back-substitute')}</span>${k(st.back)}</div>`;
      if (st.combinedTex) work += `<div class="work"><span class="eq">${/^I = /.test(st.combinedTex) ? '' : '='}</span>${k(st.combinedTex)}</div>`;
      if (st.setup || st.combinedTex || st.children.length) work += `<div class="work final"><span class="eq">=</span>${k(st.resultTex)}</div>`;
      body += work;
      return `<li class="step${open ? ' open' : ''}">
        <div class="step-row">
          <button class="twisty${hasBody ? '' : ' leaf'}" aria-label="Show details" aria-expanded="${open}">${CHEVRON}</button>
          <div class="step-eq">${st.caption ? `<span class="step-cap">${esc(st.caption)}</span>` : ''}${k(eq)}</div>
          <div class="step-tags">${st.rules.map(tag).join('')}</div>
        </div>
        ${hasBody ? `<div class="step-body">${body}</div>` : ''}
      </li>`;
    }

    // sidebar: every rule the work uses, in order of first use, with how many steps use it
    S.renderRuleList = (res) => {
      const list = el('ruleList');
      if (!res) {
        list.innerHTML = `<li class="side-empty">${cfg.rulesEmpty}</li>`;
        el('rulesMeta').textContent = '';
        return;
      }
      const count = {};
      const walk = (st) => { st.rules.forEach((r) => { count[r] = (count[r] || 0) + 1; }); st.children.forEach(walk); };
      res.steps.forEach(walk);
      const rules = res.rules.slice();
      if (cfg.hasOrder && S.n > 1) {
        if (!rules.includes('higherOrder')) rules.unshift('higherOrder');
        count.higherOrder = S.n - 1;
      }
      const items = rules.map((id) => Calc.RULE_BY_ID[id]).filter(Boolean);
      el('rulesMeta').textContent = items.length + (items.length === 1 ? ' rule' : ' rules');
      list.innerHTML = items.map((r) => {
        const cat = Calc.CATEGORIES.find((c) => c.id === r.cat);
        const n = count[r.id] || 1;
        return `<li><button class="rule-item cat-${r.cat}" data-rule="${r.id}" title="Read the ${esc(r.name)} and its proof">
          <span class="ri-name">${esc(r.name)}</span>
          <span class="ri-cat">${esc(cat ? cat.name : '')}</span>
          <span class="ri-n" title="Used in ${n} step${n > 1 ? 's' : ''}">${n > 1 ? '×' + n : ''}</span>
        </button></li>`;
      }).join('');
    };

    // hovering a rule in the sidebar lights up the steps that use it, and vice versa
    S.highlightRule = (id) => {
      const r = id && Calc.RULE_BY_ID[id];
      const out = el('output');
      if (r) out.style.setProperty('--hl', 'var(--c-' + r.cat + ')');
      $$('.step-row', out).forEach((row) => {
        row.classList.toggle('hl', !!r && !!row.querySelector(':scope > .step-tags [data-rule="' + id + '"]'));
      });
    };
    S.highlightList = (rids) => {
      $$('.rule-item', el('ruleList')).forEach((b) => b.classList.toggle('hl', rids.includes(b.dataset.rule)));
    };

    S.init = () => {
      el('examples').innerHTML = cfg.examples.map((e) => {
        let math;
        try { math = k(cfg.exampleTex(Calc.parse(e))); } catch (err) { math = esc(e); }
        return `<button class="ex-item" data-ex="${esc(e)}" title="${esc(e)}">${math}</button>`;
      }).join('');
      if (matchMedia('(max-width: 900px)').matches) el('exPanel').open = false;
      S.field = Calc.MathField.mount(el('field'), {
        label: cfg.fieldLabel,
        placeholder: cfg.placeholder,
        onChange: S.schedule,
        onEnter: () => { clearTimeout(S.timer); S.run(); },
      });
      el('text').addEventListener('input', S.schedule);
      el('text').addEventListener('keydown', (e) => { if (e.key === 'Enter') { clearTimeout(S.timer); S.run(); } });
      el('mode').addEventListener('click', () => { S.setMode(!S.textMode, true); S.run(); });
      el('varSel').addEventListener('change', () => { S.v = el('varSel').value; S.updateLabel(); S.run(); });
      if (cfg.hasOrder) el('orderSel').addEventListener('change', () => { S.n = parseInt(el('orderSel').value, 10); S.updateLabel(); S.run(); });
      el('ruleList').addEventListener('mouseleave', () => S.highlightRule(null));
      el('output').addEventListener('mouseleave', () => S.highlightList([]));
    };
    S.syncControls = () => {
      el('varSel').value = S.v;
      if (el('varSel').value !== S.v) { S.v = 'x'; el('varSel').value = 'x'; }
      if (cfg.hasOrder) el('orderSel').value = String(S.n);
      S.updateLabel();
    };
    S.owns = (node) => node && (el('ruleList').contains(node) || el('output').contains(node) || el('examples').contains(node));
    return S;
  }

  /* ---------------- the two calculators ---------------- */
  const DERIV_EXAMPLES = ['x^2', 'x^3 - 4x + 1', 'sin(x^2)', 'x^2 sin x', 'x/(x^2+1)', 'e^x cos x', 'ln(sec x + tan x)',
    'sqrt(1 - x^2)', 'x^x', 'arctan(1/x)', '2^x', 'cosh(3x)', '|x|', 'log_2(x^2+1)', 'arcsin(2x)'];
  const INT_EXAMPLES = ['x^2', '3x^2 - 4x + 1', '1/x', 'e^(3x)', 'sin(2x)', 'x cos(x^2)', 'x e^x', 'ln x', 'e^x sin x',
    '1/(x^2+4)', '(2x+3)/(x^2+3x+2)', '1/(x^2-1)', '1/(x^2(x+1))', 'sin^3 x', 'cos^2 x', 'tan x', 'sec x', 'sec^3 x',
    'sqrt(1-x^2)', 'x^2 arctan x', '1/(x^2+2x+5)', 'sin(3x)cos(2x)', '1/(1+cos x)'];

  const derive = makeSolver({
    tab: 'derive', hashKey: 'd', hasOrder: true, defaultExpr: 'x^2 sin(x)',
    ids: { field: 'fx', text: 'fxText', mode: 'modeBtn', varSel: 'varSel', orderSel: 'orderSel', label: 'ddxLabel', preview: 'preview',
      answer: 'answer', output: 'output', ruleList: 'ruleList', rulesMeta: 'rulesMeta', examples: 'examples', exPanel: 'exPanel' },
    examples: DERIV_EXAMPLES,
    exampleTex: (t) => Calc.tex(t),
    fieldLabel: 'Function to differentiate',
    placeholder: 'Type a function, e.g. x^2 sin x',
    labelTex: (S) => dOp(S.n, S.v),
    engine: (tree, v, n) => Calc.derive(tree, v, n),
    emptyTitle: 'Type a function to begin',
    emptyText: 'Pick one from the examples, or try something like <code>x^3 e^x</code> or <code>tan(ln x)</code>. Each step names the rule it uses. Click a rule to see its statement, its proof, and where it sits in the Proof Map.',
    rulesEmpty: 'Rules appear here once there is a derivative.',
    errorCard: (e) => `<div class="card hint"><h2>Couldn't differentiate that</h2><p>${esc(e.message)}</p></div>`,
    answerCard: (tree, res, S) => `<div class="card answer">
        <div class="eyebrow">Result</div>
        <div class="answer-math">${k(dOp(S.n, S.v) + '\\left[' + Calc.tex(tree) + '\\right] = ' + res.resultTex, true)}</div>
      </div>`,
  });

  const integrate = makeSolver({
    tab: 'integrate', hashKey: 'i', hasOrder: false, defaultExpr: 'x e^x',
    ids: { field: 'ifx', text: 'ifxText', mode: 'imodeBtn', varSel: 'ivarSel', label: 'idxLabel', preview: 'ipreview',
      answer: 'ianswer', output: 'ioutput', ruleList: 'iruleList', rulesMeta: 'irulesMeta', examples: 'iexamples', exPanel: 'iexPanel' },
    examples: INT_EXAMPLES,
    exampleTex: (t) => '\\int ' + (t.type === 'add' ? '\\left(' + Calc.tex(t) + '\\right)' : Calc.tex(t)) + '\\,dx',
    fieldLabel: 'Function to integrate',
    placeholder: 'Type an integrand, e.g. x e^x',
    labelTex: (S) => 'd' + vtex(S.v),
    engine: (tree, v) => Calc.integrate(tree, v),
    emptyTitle: 'Type an integrand to begin',
    emptyText: 'Pick one from the examples, or try <code>x^2 e^x</code>, <code>1/(x^2-4)</code> or <code>sin^2 x cos^3 x</code>. Each step names the technique it uses. Click a technique to see why it works and which derivative rule it reverses.',
    rulesEmpty: 'Rules appear here once there is an integral.',
    stepsNote: 'Each step leaves out its own constant. They are all collected into the single + C in the result.',
    errorCard: (e) => e.nonElementary
      ? `<div class="card hint"><h2>No elementary antiderivative</h2><p>${esc(e.message)} Elementary functions are those built from polynomials, roots, exponentials, logarithms and trig functions. No combination of them has this derivative (a theorem of Liouville).</p></div>`
      : `<div class="card hint"><h2>Couldn't integrate that</h2><p>${esc(e.message)} Try rewriting the integrand, or check whether it has an elementary antiderivative at all.</p></div>`,
    answerCard: (tree, res, S) => {
      const v = S.v, vt = vtex(v);
      const integrand = Calc.tex(tree);
      const lhs = '\\int ' + (tree.type === 'add' ? '\\left(' + integrand + '\\right)' : integrand) + '\\,d' + vt;
      let check = '';
      if (res.check) {
        let src = '';
        try { src = Calc.str(Calc.present(res.result)); } catch (e) { src = ''; }
        check = `<div class="check"><span class="lbl">Check</span>${k(dOp(1, v) + '\\left[' + res.resultTex + '\\right] = ' + res.check.tex)}
          <span class="ok" title="Verified by evaluating both sides at sample points">✓ equals the integrand</span>
          ${src ? `<button class="btn-ghost" data-differentiate="${esc(src)}" data-v="${esc(v)}">Differentiate it step by step</button>` : ''}</div>`;
      }
      return `<div class="card answer">
        <div class="eyebrow">Result</div>
        <div class="answer-math">${k(lhs + ' = ' + res.resultTex + ' + C', true)}</div>
        ${res.posOnly ? `<p class="note">Valid for ${k(vt + ' > 0')} (the substitution assumes it).</p>` : ''}
        ${check}
      </div>`;
    },
  });
  const solvers = { derive, integrate };
  const solverFor = (node) => Object.values(solvers).find((s) => s.owns(node));

  /* ---------------- state & routing ---------------- */
  const state = { tab: 'derive', rule: null };
  function readHash() {
    const p = new URLSearchParams(location.hash.slice(1));
    state.tab = p.get('tab') || (p.has('i') ? 'integrate' : 'derive');
    if (p.has('d')) derive.expr = p.get('d');
    if (p.has('i')) integrate.expr = p.get('i');
    const active = solvers[state.tab];
    if (active && p.has('v')) active.v = p.get('v');
    if (p.has('n')) derive.n = Math.max(1, Math.min(4, parseInt(p.get('n'), 10) || 1));
    state.rule = p.get('rule');
  }
  function writeHash() {
    const p = new URLSearchParams();
    if (state.tab !== 'derive') p.set('tab', state.tab);
    if (state.tab === 'derive') {
      p.set('d', derive.expr);
      if (derive.v !== 'x') p.set('v', derive.v);
      if (derive.n !== 1) p.set('n', derive.n);
    } else if (state.tab === 'integrate') {
      p.set('i', integrate.expr);
      if (integrate.v !== 'x') p.set('v', integrate.v);
    }
    if (state.rule) p.set('rule', state.rule);
    const h = '#' + p.toString();
    if (h !== location.hash) history.replaceState(null, '', h);
  }

  /* ---------------- tabs ---------------- */
  let mapApi = null;
  function showTab(tab) {
    if (!document.getElementById('tab-' + tab)) tab = 'derive';
    state.tab = tab;
    $$('.tab-btn').forEach((b) => b.setAttribute('aria-selected', String(b.dataset.tab === tab)));
    $$('.tab-panel').forEach((p) => { p.hidden = p.id !== 'tab-' + tab; });
    if (tab === 'map' && !mapApi) buildMap();
    if (tab === 'library' && !$('#library').childElementCount) buildLibrary();
    writeHash();
  }

  /* ---------------- rule drawer ---------------- */
  let lastFocus = null;
  function openRule(id, opts) {
    const r = Calc.RULE_BY_ID[id];
    if (!r) return;
    if (!$('#drawer').classList.contains('open')) lastFocus = document.activeElement;
    state.rule = id;
    writeHash();
    const cat = Calc.CATEGORIES.find((c) => c.id === r.cat);
    const badge = $('#drawerCat');
    badge.className = 'cat-badge cat-' + r.cat;
    badge.textContent = cat ? cat.name : '';
    const isInt = Calc.INT_CATS && Calc.INT_CATS.has(r.cat);
    const from = r.provedFrom.length ? r.provedFrom.map(chip).join('') : '<span class="none">Nothing. This is a starting point (a definition).</span>';
    const used = r.usedFor.length ? r.usedFor.map(chip).join('') : '<span class="none">Not used to prove other rules here.</span>';
    const tryLabel = isInt ? `Try it: ∫ ${esc(r.example || '')} dx` : `Try it: d/dx [ ${esc(r.example || '')} ]`;
    $('#drawerBody').innerHTML = `
      <h2 id="drawerTitle">${esc(r.name)}</h2>
      <div class="statement cat-${r.cat}">${k(r.statement, true)}</div>
      <p class="summary">${rich(r.summary)}</p>
      ${r.example ? `<div class="drawer-actions"><button class="btn" data-try="${esc(r.example)}" data-try-tab="${isInt ? 'integrate' : 'derive'}">${tryLabel}</button></div>` : ''}
      <h3>Proof</h3>
      <div class="proof">${proofHTML(r.proof)}</div>
      <h3>Proved from</h3>
      <div class="chip-row">${from}</div>
      <h3>Used to prove</h3>
      <div class="chip-row">${used}</div>
      <h3>Where it sits</h3>
      <p class="summary" style="margin:0 0 8px;font-size:13px">Everything this rule rests on, back to the definition of a limit, plus the rules it directly proves.</p>
      <div class="mini-map" id="miniMap"></div>
      <div class="drawer-actions"><button class="btn-ghost" data-mapfocus="${r.id}">Open in full Proof Map</button></div>`;
    const ids = Calc.ProofMap.neighbourhood(id);
    Calc.ProofMap.render($('#miniMap'), { ids, focus: id, onSelect: (x) => openRule(x), idSuffix: 'mini', hoverTrace: true, dir: 'TB' });
    $('#drawerBody').scrollTop = 0;
    const scrim = $('#scrim');
    scrim.hidden = false;
    requestAnimationFrame(() => scrim.classList.add('show'));
    $('#drawer').classList.add('open');
    $('#drawer').setAttribute('aria-hidden', 'false');
    if (!opts || !opts.noFocus) $('#drawerClose').focus({ preventScroll: true });
  }
  function closeRule() {
    state.rule = null;
    writeHash();
    $('#drawer').classList.remove('open');
    $('#drawer').setAttribute('aria-hidden', 'true');
    const scrim = $('#scrim');
    scrim.classList.remove('show');
    setTimeout(() => { scrim.hidden = true; }, 200);
    if (lastFocus && lastFocus.focus) lastFocus.focus({ preventScroll: true });
  }

  /* ---------------- library ---------------- */
  function buildLibrary() {
    const html = Calc.CATEGORIES.map((c) => {
      const rules = Calc.RULES.filter((r) => r.cat === c.id);
      if (!rules.length) return '';
      return `<section class="lib-cat cat-${c.id}" data-cat="${c.id}"><h3>${esc(c.name)}</h3><div class="lib-grid">` +
        rules.map((r) => `<button class="lib-card cat-${r.cat}" data-rule="${r.id}" data-search="${esc((r.name + ' ' + r.short + ' ' + r.id + ' ' + r.summary + ' ' + c.name).toLowerCase())}">
          <div class="nm">${esc(r.name)}</div><div class="st">${k(r.statement)}</div><div class="sm">${rich(r.summary)}</div></button>`).join('') +
        '</div></section>';
    }).join('');
    $('#library').innerHTML = html;
  }
  function filterLibrary(q) {
    q = q.trim().toLowerCase();
    $$('.lib-cat').forEach((sec) => {
      let any = false;
      $$('.lib-card', sec).forEach((c) => {
        const show = !q || c.dataset.search.includes(q);
        c.hidden = !show;
        any = any || show;
      });
      sec.hidden = !any;
    });
  }

  /* ---------------- proof map ---------------- */
  function buildMap() {
    $('#legend').innerHTML = Calc.CATEGORIES.map((c) => `<span class="chip cat-${c.id}">${esc(c.name)}</span>`).join('');
    mapApi = Calc.ProofMap.render($('#mapCanvas'), { onSelect: (id) => openRule(id), interactive: true, idSuffix: 'full' });
    requestAnimationFrame(() => mapApi.readable(0.85));
  }

  // load an expression into a calculator and show it
  function load(solver, src, v) {
    closeRule();
    showTab(solver.cfg.tab);
    if (solver.cfg.hasOrder) solver.n = 1;
    solver.v = v || 'x';
    solver.syncControls();
    solver.setSrc(src);
    solver.run();
    window.scrollTo({ top: 0, behavior: 'smooth' });
  }

  /* ---------------- events ---------------- */
  function init() {
    readHash();
    let savedMode = null;
    try { savedMode = localStorage.getItem('cs-input'); } catch (e) { /* storage unavailable */ }
    Object.values(solvers).forEach((s) => {
      s.init();
      s.setMode(savedMode === 'text', false);
      s.setSrc(s.expr);
      s.syncControls();
    });
    showTab(state.tab);
    Object.values(solvers).forEach((s) => s.run());
    if (state.rule) openRule(state.rule, { noFocus: true });

    $('#libSearch').addEventListener('input', (e) => filterLibrary(e.target.value));
    $('#drawerClose').addEventListener('click', closeRule);
    $('#scrim').addEventListener('click', closeRule);
    document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && $('#drawer').classList.contains('open')) closeRule(); });
    $('#zoomIn').addEventListener('click', () => mapApi && mapApi.zoomIn());
    $('#zoomOut').addEventListener('click', () => mapApi && mapApi.zoomOut());
    $('#zoomFit').addEventListener('click', () => mapApi && mapApi.fit());
    $('#zoomFit').title = 'Show the whole map';
    $('#themeBtn').addEventListener('click', () => {
      const root = document.documentElement;
      const cur = root.getAttribute('data-theme') || (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
      const nxt = cur === 'dark' ? 'light' : 'dark';
      root.setAttribute('data-theme', nxt);
      try { localStorage.setItem('cs-theme', nxt); } catch (e) { /* storage unavailable */ }
    });
    window.addEventListener('hashchange', () => {
      const prev = Object.fromEntries(Object.entries(solvers).map(([id, s]) => [id, [s.expr, s.v, s.n].join('|')]));
      readHash();
      Object.entries(solvers).forEach(([id, s]) => {
        if ([s.expr, s.v, s.n].join('|') !== prev[id]) { s.setSrc(s.expr); s.syncControls(); s.run(); }
      });
      showTab(state.tab);
      if (state.rule) openRule(state.rule, { noFocus: true });
      else if ($('#drawer').classList.contains('open')) closeRule();
    });

    document.addEventListener('mouseover', (e) => {
      const item = e.target.closest('.rule-list .rule-item');
      if (item) { const s = solverFor(item); if (s) s.highlightRule(item.dataset.rule); return; }
      const row = e.target.closest('.output .step-row');
      if (row) { const s = solverFor(row); if (s) s.highlightList($$(':scope > .step-tags [data-rule]', row).map((b) => b.dataset.rule)); }
    });

    // delegated clicks
    document.addEventListener('click', (e) => {
      const t = e.target;
      const tab = t.closest('.tab-btn');
      if (tab) { showTab(tab.dataset.tab); return; }
      const ruleEl = t.closest('[data-rule]');
      if (ruleEl && ruleEl.tagName === 'BUTTON') { openRule(ruleEl.dataset.rule); return; }
      const ex = t.closest('[data-ex]');
      if (ex) { const s = solverFor(ex); if (s) { s.setSrc(ex.dataset.ex); s.run(); s.focus(); } return; }
      const tr = t.closest('[data-try]');
      if (tr) { load(solvers[tr.dataset.tryTab] || derive, tr.dataset.try); return; }
      const dif = t.closest('[data-differentiate]');
      if (dif) { load(derive, dif.dataset.differentiate, dif.dataset.v); return; }
      const mf = t.closest('[data-mapfocus]');
      if (mf) {
        const id = mf.dataset.mapfocus;
        closeRule(); showTab('map');
        requestAnimationFrame(() => { mapApi.focus(id); mapApi.centerOn(id); });
        return;
      }
      const go = t.closest('[data-goto]');
      if (go) { showTab(go.dataset.goto); return; }
      const tw = t.closest('.twisty');
      if (tw && !tw.classList.contains('leaf')) {
        const li = tw.closest('.step');
        li.classList.toggle('open');
        tw.setAttribute('aria-expanded', String(li.classList.contains('open')));
        return;
      }
      const act = t.closest('[data-act]');
      if (act) {
        const openAll = act.dataset.act === 'expand';
        const scope = act.closest('.output') || document;
        $$('.step', scope).forEach((li) => {
          if (!li.querySelector(':scope > .step-body')) return;
          li.classList.toggle('open', openAll);
          const b = li.querySelector(':scope > .step-row .twisty');
          if (b) b.setAttribute('aria-expanded', String(openAll));
        });
      }
    });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
