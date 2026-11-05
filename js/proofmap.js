/* proofmap.js — layered left-to-right DAG of "rule A is proved from rule B", rendered as SVG.
 * Depth = longest path from a root (a definition); order within a column by barycentre sweeps. */
(function (root) {
  'use strict';
  const Calc = (root.Calc = root.Calc || {});
  const NS = 'http://www.w3.org/2000/svg';
  const W = 156, H = 34, COLW = 214, ROWH = 46, PAD = 24;
  const TB_GAPX = 14, TB_ROWH = 70; // top-to-bottom variant (narrow containers such as the rule drawer)

  function el(tag, attrs, parent) {
    const e = document.createElementNS(NS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  function ancestors(id, out) {
    out = out || new Set();
    const r = Calc.RULE_BY_ID[id];
    if (!r) return out;
    r.provedFrom.forEach((p) => { if (!out.has(p)) { out.add(p); ancestors(p, out); } });
    return out;
  }
  function descendants(id, out) {
    out = out || new Set();
    const r = Calc.RULE_BY_ID[id];
    if (!r) return out;
    r.usedFor.forEach((c) => { if (!out.has(c)) { out.add(c); descendants(c, out); } });
    return out;
  }

  function layout(ids, dir) {
    const set = new Set(ids);
    const R = Calc.RULE_BY_ID;
    const parents = (id) => R[id].provedFrom.filter((p) => set.has(p));
    const kids = (id) => R[id].usedFor.filter((c) => set.has(c));
    const depth = {};
    const dep = (id) => {
      if (id in depth) return depth[id];
      const ps = parents(id);
      depth[id] = ps.length ? 1 + Math.max(...ps.map(dep)) : 0;
      return depth[id];
    };
    ids.forEach(dep);
    const layers = [];
    ids.forEach((id) => (layers[depth[id]] = layers[depth[id]] || []).push(id));
    for (let i = 0; i < layers.length; i++) layers[i] = layers[i] || [];
    const catIdx = {};
    Calc.CATEGORIES.forEach((c, i) => { catIdx[c.id] = i; });
    const ruleIdx = {};
    Calc.RULES.forEach((r, i) => { ruleIdx[r.id] = i; });
    layers.forEach((L) => L.sort((a, b) => catIdx[R[a].cat] - catIdx[R[b].cat] || ruleIdx[a] - ruleIdx[b]));
    const pos = {};
    const setPos = () => layers.forEach((L) => L.forEach((id, i) => { pos[id] = i - (L.length - 1) / 2; }));
    setPos();
    const bary = (id, nb) => {
      const ns = nb(id);
      return ns.length ? ns.reduce((s, n) => s + pos[n], 0) / ns.length : pos[id];
    };
    for (let it = 0; it < 8; it++) {
      for (let d = 1; d < layers.length; d++) { layers[d].sort((a, b) => bary(a, parents) - bary(b, parents)); setPos(); }
      for (let d = layers.length - 2; d >= 0; d--) { layers[d].sort((a, b) => bary(a, kids) - bary(b, kids)); setPos(); }
    }
    const maxRows = Math.max(...layers.map((L) => L.length));
    const nodes = {};
    const tb = dir === 'TB';
    layers.forEach((L, d) => L.forEach((id, i) => {
      const slot = (maxRows - L.length) / 2 + i;
      nodes[id] = tb
        ? { id, x: PAD + slot * (W + TB_GAPX), y: PAD + d * TB_ROWH, depth: d }
        : { id, x: PAD + d * COLW, y: PAD + slot * ROWH, depth: d };
    }));
    const edges = [];
    ids.forEach((id) => parents(id).forEach((p) => edges.push({ from: p, to: id })));
    return {
      nodes, edges, layers, dir: tb ? 'TB' : 'LR',
      width: tb ? PAD * 2 + (maxRows - 1) * (W + TB_GAPX) + W : PAD * 2 + (layers.length - 1) * COLW + W,
      height: tb ? PAD * 2 + (layers.length - 1) * TB_ROWH + H : PAD * 2 + (maxRows - 1) * ROWH + H,
    };
  }

  /* render(container, { ids, focus, onSelect, interactive }) */
  function render(container, opts) {
    const ids = opts.ids || Calc.RULES.map((r) => r.id);
    const L = layout(ids, opts.dir);
    container.innerHTML = '';
    const svg = el('svg', { class: 'pmap', role: 'img', 'aria-label': 'Proof dependency map', viewBox: `0 0 ${L.width} ${L.height}` }, container);
    const defs = el('defs', {}, svg);
    const mk = el('marker', { id: 'arrow-' + (opts.idSuffix || 'm'), viewBox: '0 0 10 10', refX: '9', refY: '5', markerWidth: '7', markerHeight: '7', orient: 'auto-start-reverse' }, defs);
    el('path', { d: 'M0,0 L10,5 L0,10 z', class: 'pmap-arrow' }, mk);
    const gEdges = el('g', { class: 'pmap-edges' }, svg);
    const gNodes = el('g', { class: 'pmap-nodes' }, svg);
    const edgeEls = [];
    L.edges.forEach((e) => {
      const a = L.nodes[e.from], b = L.nodes[e.to];
      let d;
      if (L.dir === 'TB') {
        const x1 = a.x + W / 2, y1 = a.y + H, x2 = b.x + W / 2, y2 = b.y - 2;
        const dy = Math.max(24, (y2 - y1) / 2);
        d = `M${x1},${y1} C${x1},${y1 + dy} ${x2},${y2 - dy} ${x2},${y2}`;
      } else {
        const x1 = a.x + W, y1 = a.y + H / 2, x2 = b.x - 2, y2 = b.y + H / 2;
        const dx = Math.max(40, (x2 - x1) / 2);
        d = `M${x1},${y1} C${x1 + dx},${y1} ${x2 - dx},${y2} ${x2},${y2}`;
      }
      const p = el('path', { d, class: 'pmap-edge', 'marker-end': `url(#arrow-${opts.idSuffix || 'm'})` }, gEdges);
      edgeEls.push({ el: p, from: e.from, to: e.to });
    });
    const nodeEls = {};
    ids.forEach((id) => {
      const r = Calc.RULE_BY_ID[id];
      const n = L.nodes[id];
      const g = el('g', { class: 'pmap-node cat-' + r.cat, transform: `translate(${n.x},${n.y})`, tabindex: '0', role: 'button', 'aria-label': r.name }, gNodes);
      el('rect', { width: W, height: H, rx: 8, class: 'pmap-box' }, g);
      el('rect', { width: 5, height: H - 12, x: 6, y: 6, rx: 2.5, class: 'pmap-tick' }, g);
      const t = el('text', { x: 18, y: H / 2 + 4.5, class: 'pmap-label' }, g);
      t.textContent = r.short || r.name;
      const title = el('title', {}, g);
      title.textContent = r.name;
      g.addEventListener('click', () => opts.onSelect && opts.onSelect(id));
      g.addEventListener('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); opts.onSelect && opts.onSelect(id); } });
      if (opts.hoverTrace !== false) {
        g.addEventListener('mouseenter', () => trace(id, true));
        g.addEventListener('mouseleave', () => trace(focusId, false));
        g.addEventListener('focus', () => trace(id, true));
        g.addEventListener('blur', () => trace(focusId, false));
      }
      nodeEls[id] = g;
    });

    let focusId = opts.focus || null;
    function trace(id, hover) {
      svg.classList.toggle('tracing', !!id);
      if (!id) {
        Object.values(nodeEls).forEach((g) => g.classList.remove('anc', 'desc', 'self'));
        edgeEls.forEach((e) => e.el.classList.remove('anc', 'desc'));
        return;
      }
      const anc = ancestors(id), des = descendants(id);
      Object.entries(nodeEls).forEach(([k, g]) => {
        g.classList.toggle('self', k === id);
        g.classList.toggle('anc', anc.has(k));
        g.classList.toggle('desc', des.has(k));
      });
      edgeEls.forEach((e) => {
        e.el.classList.toggle('anc', (anc.has(e.from) || e.from === id) && (anc.has(e.to) || e.to === id));
        e.el.classList.toggle('desc', (des.has(e.to) || e.to === id) && (des.has(e.from) || e.from === id));
      });
    }
    trace(focusId);

    /* pan & zoom by manipulating the viewBox */
    const vb = { x: 0, y: 0, w: L.width, h: L.height };
    const apply = () => svg.setAttribute('viewBox', `${vb.x} ${vb.y} ${vb.w} ${vb.h}`);
    function fit() { vb.x = 0; vb.y = 0; vb.w = L.width; vb.h = L.height; apply(); }
    function zoom(f, cx, cy) {
      const nw = Math.min(L.width * 3, Math.max(240, vb.w * f));
      const k = nw / vb.w;
      if (cx === undefined) { cx = vb.x + vb.w / 2; cy = vb.y + vb.h / 2; }
      vb.x = cx - (cx - vb.x) * k; vb.y = cy - (cy - vb.y) * k;
      vb.w = nw; vb.h = vb.h * k;
      apply();
    }
    function toSvg(ev) {
      const r = svg.getBoundingClientRect();
      // preserveAspectRatio xMidYMid meet: compute the actual scale
      const s = Math.max(vb.w / r.width, vb.h / r.height);
      const ox = (r.width * s - vb.w) / 2, oy = (r.height * s - vb.h) / 2;
      return { x: vb.x - ox + (ev.clientX - r.left) * s, y: vb.y - oy + (ev.clientY - r.top) * s, s };
    }
    if (opts.interactive) {
      svg.classList.add('interactive');
      svg.addEventListener('wheel', (ev) => {
        ev.preventDefault();
        const p = toSvg(ev);
        zoom(Math.exp(ev.deltaY * 0.0015), p.x, p.y);
      }, { passive: false });
      let drag = null;
      svg.addEventListener('pointerdown', (ev) => {
        if (ev.target.closest('.pmap-node')) return;
        drag = { x: ev.clientX, y: ev.clientY, vx: vb.x, vy: vb.y, s: toSvg(ev).s };
        svg.setPointerCapture(ev.pointerId);
        svg.classList.add('dragging');
      });
      svg.addEventListener('pointermove', (ev) => {
        if (!drag) return;
        vb.x = drag.vx - (ev.clientX - drag.x) * drag.s;
        vb.y = drag.vy - (ev.clientY - drag.y) * drag.s;
        apply();
      });
      const end = () => { drag = null; svg.classList.remove('dragging'); };
      svg.addEventListener('pointerup', end);
      svg.addEventListener('pointercancel', end);
    }
    // Start at a legible scale (≈ scale px per unit), anchored at the left edge, instead of fitting everything.
    function readable(scale) {
      const r = svg.getBoundingClientRect();
      if (!r.width || !r.height) return fit();
      const s = Math.max(scale, Math.min(r.width / L.width, r.height / L.height));
      vb.w = r.width / s; vb.h = r.height / s;
      vb.x = Math.min(0, (L.width - vb.w) / 2);
      vb.y = L.height / 2 - vb.h / 2;
      apply();
    }
    return {
      svg, layout: L, fit, readable, zoomIn: () => zoom(1 / 1.25), zoomOut: () => zoom(1.25),
      focus(id) { focusId = id; trace(id); },
      centerOn(id) {
        const n = L.nodes[id];
        if (!n) return;
        const r = svg.getBoundingClientRect();
        const s = r.width ? Math.max(0.85, Math.min(r.width / L.width, r.height / L.height)) : 1;
        vb.w = (r.width || 900) / s; vb.h = (r.height || 600) / s;
        vb.x = n.x + W / 2 - vb.w / 2; vb.y = n.y + H / 2 - vb.h / 2;
        apply();
      },
    };
  }

  // The subgraph worth showing beside one rule: everything it rests on, plus what it directly proves.
  function neighbourhood(id) {
    const s = ancestors(id);
    s.add(id);
    (Calc.RULE_BY_ID[id].usedFor || []).forEach((c) => s.add(c));
    return Calc.RULES.map((r) => r.id).filter((x) => s.has(x));
  }

  Calc.ProofMap = { render, layout, ancestors, descendants, neighbourhood };
})(typeof window !== 'undefined' ? window : globalThis);
