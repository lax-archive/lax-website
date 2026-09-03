// The reflow paper surface: joins the pre-rendered cards to the anchor
// elements the vendored ReflowTeX viewer emits (`[data-mark][data-side]`,
// re-anchored by the viewer on every reflow), paints each passage's
// highlight and shadow over the text, stacks the cards beside their
// passages, draws the gutter band from each passage's shadow to its card,
// and owns the view toggle (the page opens on the paper as printed) and the
// `#m<n>` deep links into the reflowed text.
// The join is structural — anchor offsets only, no text matching and no
// geometry from the PDF. The placement and outline math is pure and lives
// up top so node:vm can test it the way manuscript-place.js is tested.
(() => {
  'use strict';

  // ---- pure placement (no DOM; exposed for tests) ----

  // From measured anchors [{n, side: "b"|"e", top, bottom?, x?, inline?}]
  // to one vertical band per mark: top = the begin anchor's line top,
  // bottom = the furthest end anchor's line bottom (clamped so bottom >=
  // top), with those two anchors kept as `begin` and `end` for the outline.
  // An anchor without `bottom` is a point. A mark with only one side
  // collapses to that side; a mark with neither is absent, and its card
  // goes unplaced.
  function bands(anchors) {
    const out = {};
    for (const a of anchors) {
      if (!a || !Number.isFinite(a.n) || !Number.isFinite(a.top)) continue;
      const band = out[a.n] || (out[a.n] = { top: Infinity, bottom: -Infinity });
      if (a.side === 'e') {
        const bottom = Number.isFinite(a.bottom) ? a.bottom : a.top;
        if (bottom > band.bottom) { band.bottom = bottom; band.end = a; }
      } else if (a.top < band.top) { band.top = a.top; band.begin = a; }
    }
    for (const n of Object.keys(out)) {
      const band = out[n];
      if (band.top === Infinity) band.top = band.bottom;
      if (band.bottom === -Infinity) band.bottom = band.top;
      if (band.bottom < band.top) band.bottom = band.top;
    }
    return out;
  }

  // Stack the cards in rail order: a placed card wants its band's top (less
  // `offset`, the rail's own top in the shared space); a card whose mark has
  // no band follows the one before it. In the given order a card that would
  // overlap its predecessor is pushed down by `gap` — the same rule the PDF
  // surface uses (laxManuscript.stackCards).
  function place(cards, bandsByMark, gap, offset) {
    const tops = [];
    const placed = [];
    let cursor = -Infinity;
    for (const card of cards) {
      const band = bandsByMark[card.n];
      const has = band !== undefined;
      const want = has ? Math.max(0, band.top - offset) : (cursor === -Infinity ? 0 : cursor + gap);
      const top = Math.max(want, cursor === -Infinity ? want : cursor + gap);
      tops.push(top);
      placed.push(has);
      cursor = top + card.height;
    }
    return { tops, placed };
  }

  // A passage's flat region over a column of `width`: the split-diff shape
  // the PDF surface paints per column run — the begin anchor's line from
  // the anchor to the column's right edge, every line between at full
  // width, the end anchor's line from the left edge to the anchor. An
  // anchor in the stream (not `inline`) spans the whole column, and a
  // passage whose end sits on its begin line is one box between the two.
  // Returns the polygon's points, [[x, y], ...].
  function outline(band, width) {
    const b = band.begin;
    const e = band.end;
    const bx = b && b.inline ? Math.min(Math.max(0, b.x), width) : 0;
    const bt = band.top;
    const bb = b && Number.isFinite(b.bottom) ? Math.max(bt, b.bottom) : bt;
    const ex = e && e.inline ? Math.min(Math.max(0, e.x), width) : width;
    const eb = band.bottom;
    const et = e ? Math.min(eb, e.top) : eb;
    const points = et <= bb
      ? [[bx, bt], [Math.max(bx, ex), bt], [Math.max(bx, ex), eb], [bx, eb]]
      : [[bx, bt], [width, bt], [width, et], [ex, et], [ex, eb], [0, eb], [0, bb], [bx, bb]];
    // A passage that begins or ends in the stream spans the whole column, so
    // its corners coincide; drop the repeats to keep the polygon simple.
    const out = [];
    for (const [x, y] of points) {
      const last = out[out.length - 1];
      if (!last || last[0] !== x || last[1] !== y) out.push([x, y]);
    }
    const first = out[0];
    const last = out[out.length - 1];
    if (out.length > 1 && first[0] === last[0] && first[1] === last[1]) out.pop();
    return out;
  }

  // Whether (x, y) lies inside the polygon, by ray casting.
  function contains(points, x, y) {
    let inside = false;
    for (let i = 0, j = points.length - 1; i < points.length; j = i++) {
      const [xi, yi] = points[i];
      const [xj, yj] = points[j];
      if ((yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  const api = { bands, place, outline, contains };
  if (typeof window !== 'undefined') window.laxReflowPlace = api;
  else if (typeof globalThis !== 'undefined') globalThis.laxReflowPlace = api;
  if (typeof document === 'undefined') return;

  // ---- DOM glue ----

  const root = document.querySelector('.manuscript');
  const reflowBody = document.getElementById('manuscript-reflow');
  const docEl = document.getElementById('manuscript-reflow-doc');
  const railEl = document.getElementById('manuscript-rail-reflow');
  const linksEl = document.getElementById('manuscript-reflow-links');
  const pdfSurface = document.getElementById('manuscript-pdf');
  if (!root || !reflowBody || !docEl || !railEl) return;

  const CARD_GAP = 8;
  const LINE_ABOVE = 14;    // px above an in-paragraph anchor's baseline to its line's top
  const LINE_BELOW = 6;     // px below that baseline to the line's bottom
  const STREAM_PAD = 4;     // px a stream anchor's passage reaches beyond its blocks
  const SHADOW_MARGIN = 12; // px the shadow runs beyond the text column on each side
  const SVG = 'http://www.w3.org/2000/svg';

  const cards = [...railEl.querySelectorAll('.manuscript-card[data-mark]')].map((el) => ({
    n: Number(el.dataset.mark), el, kind: `kind-${[...el.classList].find((c) => c.startsWith('kind-'))?.slice(5) || 'concept'}`,
    band: null, points: null, shadow: null, shape: null, link: null, pinned: false,
  }));

  function svgNode(name, attrs) {
    const node = document.createElementNS(SVG, name);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
    return node;
  }

  // The highlight layer over the document, the PDF surface's per-page layer
  // in one: the shadows behind the passages' regions, multiplied onto the text.
  const hlEl = svgNode('svg', { class: 'manuscript-hl-layer', 'aria-hidden': 'true' });
  const shadowsEl = svgNode('g', {});
  const shapesEl = svgNode('g', {});
  hlEl.append(shadowsEl, shapesEl);
  docEl.append(hlEl);

  // ---- the view toggle ----

  const buttons = [...root.querySelectorAll('.manuscript-view-button')];
  function show(view) {
    reflowBody.hidden = view !== 'reflow';
    if (pdfSurface) pdfSurface.hidden = view !== 'pdf';
    for (const button of buttons) button.setAttribute('aria-pressed', String(button.dataset.view === view));
    // The page opens on the paper as printed, so the reflow surface lays out
    // while hidden — the viewer keeps that first layout until the element has
    // a real width, which showing it gives; its own observer then re-lays out
    // and the reflow event brings the cards along.
    if (view === 'reflow') schedule();
  }
  for (const button of buttons) button.addEventListener('click', () => show(button.dataset.view));

  // ---- the anchor join ----

  // Every anchor with the vertical extent of the line it sits on, in the
  // document's coordinates. An in-paragraph anchor is pinned at its
  // baseline (the viewer positions it absolutely); a stream anchor sits in
  // flow before its passage's first block or after its last, so its extent
  // is that block's edge, padded — a begin anchor's block is the next mount
  // (the anchor stands above the mount's margin), an end anchor's is the
  // previous, whose bottom edge the zero-size anchor already sits on.
  function measureAnchors() {
    const box = docEl.getBoundingClientRect();
    return [...docEl.querySelectorAll('.latex-anchor[data-mark]')].map((a) => {
      const r = a.getBoundingClientRect();
      const side = a.dataset.side === 'e' ? 'e' : 'b';
      const inline = a.style.position === 'absolute';
      const x = r.left - box.left;
      let top = r.top - box.top;
      let bottom = top;
      if (inline) {
        top -= LINE_ABOVE;
        bottom += LINE_BELOW;
      } else if (side === 'b') {
        let next = a.nextElementSibling;
        while (next && next.classList.contains('latex-anchor')) next = next.nextElementSibling;
        if (next) top = next.getBoundingClientRect().top - box.top;
        top -= STREAM_PAD;
        bottom = top;
      } else {
        bottom += STREAM_PAD;
        top = bottom;
      }
      return { n: Number(a.dataset.mark), side, top, bottom, x, inline };
    });
  }

  function placeCards() {
    if (reflowBody.hidden || !cards.length) return;
    const bodyBox = reflowBody.getBoundingClientRect();
    const docTop = docEl.getBoundingClientRect().top - bodyBox.top;
    const railTop = railEl.getBoundingClientRect().top - bodyBox.top;
    const byMark = bands(measureAnchors());
    railEl.classList.add('manuscript-rail-live');
    const result = place(cards.map((card) => ({ n: card.n, height: card.el.offsetHeight })), byMark, CARD_GAP, railTop - docTop);
    let bottom = 0;
    cards.forEach((card, index) => {
      card.el.style.top = `${result.tops[index]}px`;
      card.el.classList.toggle('manuscript-card-unplaced', !result.placed[index]);
      card.band = byMark[card.n] || null;
      bottom = Math.max(bottom, result.tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(docEl.offsetHeight, bottom + 24)}px`;
    paintHighlights();
    drawLinks();
  }

  // Per passage: its flat region along the text, and behind it a lighter
  // shadow a fixed margin beyond the column on both sides, from the
  // passage's first line to its last. The gutter band starts at the
  // shadow's right edge. Coordinates are the document's.
  function paintHighlights() {
    const width = docEl.clientWidth;
    hlEl.setAttribute('viewBox', `0 0 ${width} ${docEl.clientHeight}`);
    for (const card of cards) {
      if (!card.band) {
        if (card.shape) { card.shape.remove(); card.shape = null; }
        if (card.shadow) { card.shadow.remove(); card.shadow = null; }
        card.points = null;
        continue;
      }
      card.points = outline(card.band, width);
      if (!card.shape) {
        card.shape = svgNode('path', { class: `manuscript-hl ${card.kind}` });
        shapesEl.append(card.shape);
      }
      card.shape.setAttribute('d', `M${card.points.map(([x, y]) => `${x.toFixed(1)},${y.toFixed(1)}`).join('L')}Z`);
      if (!card.shadow) {
        card.shadow = svgNode('rect', { class: `manuscript-hl-shadow ${card.kind}` });
        shadowsEl.append(card.shadow);
      }
      card.shadow.setAttribute('x', String(-SHADOW_MARGIN));
      card.shadow.setAttribute('y', card.band.top.toFixed(1));
      card.shadow.setAttribute('width', String(width + 2 * SHADOW_MARGIN));
      card.shadow.setAttribute('height', (card.band.bottom - card.band.top).toFixed(1));
    }
  }

  // The band from a passage to its card, the PDF surface's split-diff shape:
  // the passage's shadow at its right edge, the whole card at the rail's
  // left edge, cubic curves across the gutter. Coordinates are the reflow
  // body's; the band starts a pixel inside the shadow so the two meet
  // without a seam.
  function drawLinks() {
    if (!linksEl) return;
    linksEl.setAttribute('viewBox', `0 0 ${reflowBody.clientWidth} ${reflowBody.clientHeight}`);
    linksEl.classList.add('manuscript-links-live');
    const bodyBox = reflowBody.getBoundingClientRect();
    const docBox = docEl.getBoundingClientRect();
    const docTop = docBox.top - bodyBox.top;
    const xl = docBox.left - bodyBox.left + docEl.clientWidth + SHADOW_MARGIN - 1;
    const xr = railEl.offsetLeft + 2;
    const xm = (xl + xr) / 2;
    for (const card of cards) {
      if (!card.band) {
        if (card.link) { card.link.remove(); card.link = null; }
        continue;
      }
      const top = docTop + card.band.top;
      const bottom = docTop + card.band.bottom;
      const ct = railEl.offsetTop + card.el.offsetTop;
      const cb = ct + card.el.offsetHeight;
      const d = `M${xl},${top.toFixed(1)} C${xm},${top.toFixed(1)} ${xm},${ct} ${xr},${ct} L${xr},${cb} C${xm},${cb} ${xm},${bottom.toFixed(1)} ${xl},${bottom.toFixed(1)} Z`;
      if (!card.link) {
        card.link = svgNode('path', { class: `manuscript-link ${card.kind}` });
        linksEl.append(card.link);
      }
      card.link.setAttribute('d', d);
    }
  }

  // ---- cards: hover opens, click pins, like the PDF surface ----

  // The card in front: its region, shadow, and band drawn over the others.
  function raise(card) {
    if (card.shape && shapesEl.lastElementChild !== card.shape) shapesEl.append(card.shape);
    if (card.shadow && shadowsEl.lastElementChild !== card.shadow) shadowsEl.append(card.shadow);
    if (card.link && linksEl && linksEl.lastElementChild !== card.link) linksEl.append(card.link);
  }

  function hits(card) {
    return [card.shape, card.shadow, card.link].filter(Boolean);
  }

  function isExpanded(card) {
    return card.el.classList.contains('manuscript-card-expanded');
  }

  function setExpanded(card, expanded) {
    card.el.classList.toggle('manuscript-card-expanded', expanded);
    const body = card.el.querySelector('.manuscript-card-body');
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (body) body.hidden = !expanded;
    if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
    for (const hit of hits(card)) hit.classList.toggle(hit === card.link ? 'manuscript-link-active' : 'manuscript-hl-active', expanded);
    if (expanded) raise(card);
    placeCards();
  }

  function setHover(card, hovering) {
    for (const hit of hits(card)) hit.classList.toggle(hit === card.link ? 'manuscript-link-hover' : 'manuscript-hl-hover', hovering);
    if (hovering) raise(card);
    if (!card.pinned && isExpanded(card) !== hovering) setExpanded(card, hovering);
  }

  function setPinned(card, pinned) {
    card.pinned = pinned;
    card.el.classList.toggle('manuscript-card-pinned', pinned);
    if (isExpanded(card) !== pinned) setExpanded(card, pinned);
  }

  // A flash is a moment of the hover fill on the passage's highlight.
  function flash(card) {
    const targets = [card.shape, card.shadow].filter(Boolean);
    for (const hit of targets) hit.classList.add('manuscript-hl-flash');
    setTimeout(() => { for (const hit of targets) hit.classList.remove('manuscript-hl-flash'); }, 1200);
  }

  function scrollToPassage(card) {
    const anchor = docEl.querySelector(`.latex-anchor[data-mark="${card.n}"][data-side="b"]`);
    if (anchor) anchor.scrollIntoView({ behavior: 'smooth', block: 'start' });
    flash(card);
  }

  for (const card of cards) {
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (toggle) toggle.addEventListener('click', (event) => {
      event.stopPropagation();
      setPinned(card, !card.pinned);
    });
    card.el.addEventListener('click', (event) => {
      if (event.target.closest('a, button')) return;
      setPinned(card, !card.pinned);
      scrollToPassage(card);
    });
    card.el.addEventListener('mouseenter', () => setHover(card, true));
    card.el.addEventListener('mouseleave', () => setHover(card, false));
  }

  // ---- the passages: hover opens their cards, click pins ----
  //
  // The highlight layer takes no pointer events so the text under it stays
  // selectable; hovers and clicks are hit-tested here against the regions
  // (the innermost passage winning) and then the shadows (the shortest).
  function cardAt(event) {
    if (event.target.closest('.manuscript-rail, a')) return null;
    const box = docEl.getBoundingClientRect();
    const x = event.clientX - box.left;
    const y = event.clientY - box.top;
    let best = null;
    let bestSpan = Infinity;
    for (const card of cards) {
      if (!card.points || !contains(card.points, x, y)) continue;
      const span = card.band.bottom - card.band.top;
      if (span < bestSpan) { best = card; bestSpan = span; }
    }
    if (best) return best;
    const width = docEl.clientWidth;
    if (x < -SHADOW_MARGIN || x > width + SHADOW_MARGIN) return null;
    for (const card of cards) {
      if (!card.band || y < card.band.top || y > card.band.bottom) continue;
      const span = card.band.bottom - card.band.top;
      if (span < bestSpan) { best = card; bestSpan = span; }
    }
    return best;
  }
  let hovered = null;
  function hover(card) {
    if (card === hovered) return;
    if (hovered) { setHover(hovered, false); hovered.el.classList.remove('manuscript-card-hover'); }
    hovered = card;
    if (hovered) { setHover(hovered, true); hovered.el.classList.add('manuscript-card-hover'); }
  }
  reflowBody.addEventListener('mousemove', (event) => {
    if (event.target.closest('.manuscript-rail')) return;
    hover(cardAt(event));
  });
  reflowBody.addEventListener('mouseleave', () => hover(null));
  reflowBody.addEventListener('click', (event) => {
    if (event.target.closest('.manuscript-rail')) return;
    const best = cardAt(event);
    if (!best) return;
    const pinned = !best.pinned;
    setPinned(best, pinned);
    flash(best);
    // Brings the card into view where the rail is scrolled off to the side.
    if (pinned) best.el.scrollIntoView({ behavior: 'smooth', block: 'nearest', inline: 'nearest' });
  });

  // ---- deep links: #m<n> lands on the passage, and opens its card ----
  //
  // The anchor does not exist when the browser first tries the fragment (the
  // viewer builds it after DOMContentLoaded), and Chromium re-processes the
  // missing fragment around `load`, resetting any scroll done in between. So
  // the hash is honoured on every placement pass for a short settling window
  // — font waves reflow the text once or twice in the first second — and
  // stops the moment the reader moves.
  let userMoved = false;
  let hashPinned = false;
  const anchorUntil = performance.now() + 3000;
  for (const type of ['wheel', 'touchstart', 'pointerdown', 'keydown'])
    window.addEventListener(type, () => { userMoved = true; }, { passive: true, once: true });

  function honourHash() {
    const match = /^#m(\d+)$/.exec(location.hash);
    if (!match) return;
    // Only this surface's business while it is the one showing: the printed
    // surface honours the same fragment on its own cards (manuscript.js), and
    // a link must not move the reader off the view they opened.
    if (reflowBody.hidden) return;
    const card = cards.find((c) => c.n === Number(match[1]));
    if (card && !hashPinned) {
      hashPinned = true;
      setPinned(card, true);
      flash(card);
    }
    const anchor = document.getElementById(`m${match[1]}`);
    if (anchor && docEl.contains(anchor)) anchor.scrollIntoView({ block: 'start' });
  }

  // ---- scheduling: re-place on every viewer reflow and page resize ----

  let scheduled = false;
  function schedule() {
    if (scheduled) return;
    scheduled = true;
    requestAnimationFrame(() => {
      scheduled = false;
      placeCards();
      if (!userMoved && performance.now() < anchorUntil) honourHash();
    });
  }

  document.addEventListener('latex-viewer:reflow', schedule);
  window.addEventListener('resize', schedule);
  window.addEventListener('hashchange', () => { hashPinned = false; honourHash(); });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(schedule);
})();
