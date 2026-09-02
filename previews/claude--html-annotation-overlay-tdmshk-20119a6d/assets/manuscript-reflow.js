// The reflow paper surface: joins the pre-rendered cards to the anchor
// elements the vendored ReflowTeX viewer emits (`[data-mark][data-side]`,
// re-anchored by the viewer on every reflow), stacks the cards beside their
// passages, draws the gutter band from each passage's begin/end anchors to
// its card, and owns the reflow/PDF view toggle and the `#m<n>` deep links.
// The join is structural — anchor offsets only, no text matching and no
// geometry from the PDF. The placement math is pure and lives up top so
// node:vm can test it the way manuscript-place.js is tested.
(() => {
  'use strict';

  // ---- pure placement (no DOM; exposed for tests) ----

  // From measured anchors [{n, side: "b"|"e", top}] to one vertical band per
  // mark: top = the begin anchor, bottom = the furthest end anchor (clamped
  // so bottom >= top). A mark with only one side collapses to that side; a
  // mark with neither is absent, and its card goes unplaced.
  function bands(anchors) {
    const out = {};
    for (const a of anchors) {
      if (!a || !Number.isFinite(a.n) || !Number.isFinite(a.top)) continue;
      const band = out[a.n] || (out[a.n] = { top: Infinity, bottom: -Infinity });
      if (a.side === 'e') band.bottom = Math.max(band.bottom, a.top);
      else band.top = Math.min(band.top, a.top);
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

  const api = { bands, place };
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
  const BAND_ABOVE = 14; // px above an anchor's baseline to the line's top
  const BAND_BELOW = 6;  // px below the end anchor's baseline
  const SVG = 'http://www.w3.org/2000/svg';

  const cards = [...railEl.querySelectorAll('.manuscript-card[data-mark]')].map((el) => ({
    n: Number(el.dataset.mark), el, band: null, link: null, pinned: false,
  }));

  // ---- the view toggle ----

  const buttons = [...root.querySelectorAll('.manuscript-view-button')];
  let pdfStarted = false;
  function show(view) {
    reflowBody.hidden = view !== 'reflow';
    if (pdfSurface) pdfSurface.hidden = view !== 'pdf';
    for (const button of buttons) button.setAttribute('aria-pressed', String(button.dataset.view === view));
    // The PDF loads on first switch only (manuscript.js waits for this event
    // on deferred pages); unhide first so its layout measures real widths.
    if (view === 'pdf' && pdfSurface && !pdfStarted) {
      pdfStarted = true;
      document.dispatchEvent(new CustomEvent('lax:show-pdf'));
    }
    if (view === 'reflow') schedule();
  }
  for (const button of buttons) button.addEventListener('click', () => show(button.dataset.view));

  // ---- the anchor join ----

  function measureAnchors() {
    const box = reflowBody.getBoundingClientRect();
    return [...docEl.querySelectorAll('.latex-anchor[data-mark]')].map((a) => {
      const r = a.getBoundingClientRect();
      return { n: Number(a.dataset.mark), side: a.dataset.side === 'e' ? 'e' : 'b', top: r.top - box.top };
    });
  }

  function placeCards() {
    if (reflowBody.hidden || !cards.length) return;
    const bodyBox = reflowBody.getBoundingClientRect();
    const railTop = railEl.getBoundingClientRect().top - bodyBox.top;
    const byMark = bands(measureAnchors());
    railEl.classList.add('manuscript-rail-live');
    const result = place(cards.map((card) => ({ n: card.n, height: card.el.offsetHeight })), byMark, CARD_GAP, railTop + BAND_ABOVE);
    let bottom = 0;
    cards.forEach((card, index) => {
      card.el.style.top = `${result.tops[index]}px`;
      card.el.classList.toggle('manuscript-card-unplaced', !result.placed[index]);
      card.band = byMark[card.n] || null;
      bottom = Math.max(bottom, result.tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(docEl.offsetHeight, bottom + 24)}px`;
    drawLinks();
  }

  // The band from a passage to its card, the PDF surface's split-diff shape:
  // the passage's edge from its begin to its end anchor, the whole card at
  // the rail's left edge, cubic curves across the gutter. Coordinates are
  // the reflow body's.
  function drawLinks() {
    if (!linksEl) return;
    linksEl.setAttribute('viewBox', `0 0 ${reflowBody.clientWidth} ${reflowBody.clientHeight}`);
    linksEl.classList.add('manuscript-links-live');
    const xl = docEl.offsetLeft + docEl.offsetWidth - 1;
    const xr = railEl.offsetLeft + 2;
    const xm = (xl + xr) / 2;
    for (const card of cards) {
      if (!card.band) {
        if (card.link) { card.link.remove(); card.link = null; }
        continue;
      }
      const top = card.band.top - BAND_ABOVE;
      const bottom = card.band.bottom + BAND_BELOW;
      const ct = railEl.offsetTop + card.el.offsetTop;
      const cb = ct + card.el.offsetHeight;
      const d = `M${xl},${top.toFixed(1)} C${xm},${top.toFixed(1)} ${xm},${ct} ${xr},${ct} L${xr},${cb} C${xm},${cb} ${xm},${bottom.toFixed(1)} ${xl},${bottom.toFixed(1)} Z`;
      if (!card.link) {
        card.link = document.createElementNS(SVG, 'path');
        card.link.setAttribute('class', `manuscript-link kind-${[...card.el.classList].find((c) => c.startsWith('kind-'))?.slice(5) || 'concept'}`);
        linksEl.append(card.link);
      }
      card.link.setAttribute('d', d);
    }
  }

  // ---- cards: hover opens, click pins, like the PDF surface ----

  function raise(card) {
    if (card.link && linksEl && linksEl.lastElementChild !== card.link) linksEl.append(card.link);
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
    if (card.link) card.link.classList.toggle('manuscript-link-active', expanded);
    if (expanded) raise(card);
    placeCards();
  }

  function setHover(card, hovering) {
    if (card.link) card.link.classList.toggle('manuscript-link-hover', hovering);
    if (hovering) raise(card);
    if (!card.pinned && isExpanded(card) !== hovering) setExpanded(card, hovering);
  }

  function setPinned(card, pinned) {
    card.pinned = pinned;
    card.el.classList.toggle('manuscript-card-pinned', pinned);
    if (isExpanded(card) !== pinned) setExpanded(card, pinned);
  }

  function scrollToPassage(card) {
    const anchor = docEl.querySelector(`.latex-anchor[data-mark="${card.n}"][data-side="b"]`);
    if (anchor) anchor.scrollIntoView({ behavior: 'smooth', block: 'start' });
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
    const card = cards.find((c) => c.n === Number(match[1]));
    if (card && !hashPinned) {
      hashPinned = true;
      show('reflow');
      setPinned(card, true);
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
