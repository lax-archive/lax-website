// The reflow paper page: joins the pre-rendered cards to the anchor
// elements the vendored ReflowTeX viewer emits (`[data-mark][data-side]`,
// re-anchored by the viewer on every reflow), paints each passage's
// highlight and shadow over the text, and honours the `#m<n>` deep links
// into the reflowed text. Beside the text — the rail — the cards stack at
// their passages' height with a gutter band from each passage's shadow to
// its card, opening on hover and pinned by a click. On a narrow screen
// there is no room beside the text: the rail is gone, a tap on a passage
// opens its card in the text right under the passage (the viewer keeps a
// slot after the passage's last line), and a tap on the card, its ×, or
// the passage again closes it.
// The paper's footnotes become sidenotes in the same rail: the viewer lays
// the footnote text out as endnotes (its own `.latex-footnote` segment per
// footnote, behind a `.latex-footnote-rule`) and marks each reference point
// with a `.latex-fnref[data-footnote]` anchor; this script lifts each
// segment — the one element, so the viewer's repaints keep reaching it —
// into a `.manuscript-footnote` card stacked with the mark cards at its
// reference's line, asks the viewer to set it at the card's measure, and
// hides the endnotes. Where the rail is not beside the text (the narrow
// layout, or a body that scrolls sideways), the endnotes stay in flow and
// no sidenote card shows.
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
  // goes unplaced. `n` is a mark's number, or any non-empty string key —
  // a footnote's reference is `fn:<k>`, a begin-side point.
  function bands(anchors) {
    const out = {};
    for (const a of anchors) {
      if (!a || !validKey(a.n) || !Number.isFinite(a.top)) continue;
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

  function validKey(n) {
    return typeof n === 'number' ? Number.isFinite(n) : typeof n === 'string' && n !== '';
  }

  // Stack the cards top to bottom by their bands: a placed card wants its
  // band's top (less `offset`, the rail's own top in the shared space); a
  // card whose mark has no band follows the card before it in rail order.
  // The marks come in the record's order, which need not be the text's, so
  // the cards are sorted by what they want first (a card stacked in rail
  // order behind one from further down would sit far below its passage);
  // cards wanting the same y keep their rail order. Then a card that would
  // overlap its predecessor is pushed down by `gap` — the same rule the PDF
  // surface uses (laxManuscript.stackCards). `tops` and `placed` are in
  // rail order. Footnote cards are cards like any other here: keyed
  // `fn:<k>`, wanting their reference's line.
  function place(cards, bandsByMark, gap, offset) {
    const wants = [];
    const keys = [];
    cards.forEach((card, index) => {
      const band = bandsByMark[card.n];
      wants.push(band !== undefined ? Math.max(0, band.top - offset) : null);
      keys.push(wants[index] !== null ? wants[index] : index > 0 ? keys[index - 1] : 0);
    });
    const order = cards.map((card, index) => index).sort((a, b) => keys[a] - keys[b] || a - b);
    const tops = new Array(cards.length);
    const placed = wants.map((want) => want !== null);
    let cursor = -Infinity;
    for (const index of order) {
      const follow = cursor === -Infinity ? 0 : cursor + gap;
      const top = Math.max(wants[index] !== null ? wants[index] : follow, follow);
      tops[index] = top;
      cursor = top + cards[index].height;
    }
    return { tops, placed };
  }

  // The rail order the cards should have: by their bands' tops (document
  // position), a card without a band keeping its place after the card
  // before it, ties keeping the order given. Returns the indices in that
  // order — the mark cards come in the record's order and the footnote
  // cards join them as the viewer reveals them, so the rail is re-sorted
  // on every placement and the DOM follows (tab order, and place()'s
  // follow rule for an unbanded card, both read the rail order).
  function railOrder(cards, bandsByMark) {
    const keys = [];
    cards.forEach((card, index) => {
      const band = bandsByMark[card.n];
      keys.push(band !== undefined ? band.top : index > 0 ? keys[index - 1] : -Infinity);
    });
    return cards.map((card, index) => index).sort((a, b) => keys[a] - keys[b] || a - b);
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

  const api = { bands, place, railOrder, outline, contains };
  if (typeof window !== 'undefined') window.laxReflowPlace = api;
  else if (typeof globalThis !== 'undefined') globalThis.laxReflowPlace = api;
  if (typeof document === 'undefined') return;

  // ---- DOM glue ----

  const root = document.querySelector('.manuscript');
  const reflowBody = document.getElementById('manuscript-reflow');
  const docEl = document.getElementById('manuscript-reflow-doc');
  const railEl = document.getElementById('manuscript-rail-reflow');
  const linksEl = document.getElementById('manuscript-reflow-links');
  const footnoteTemplate = document.getElementById('manuscript-footnote-card');
  if (!root || !reflowBody || !docEl || !railEl) return;

  const CARD_GAP = 8;
  const LINE_ABOVE = 14;    // px above an in-paragraph anchor's baseline to its line's top
  const LINE_BELOW = 6;     // px below that baseline to the line's bottom
  const STREAM_PAD = 4;     // px a stream anchor's passage reaches beyond its blocks
  const SHADOW_MARGIN = 12; // px the shadow runs beyond the text column on each side
  const SAME_BAND = 3;      // px within which two passages count as one (a theorem marked thrice)
  const SVG = 'http://www.w3.org/2000/svg';

  // The rail's cards: the mark cards the page shipped (`fn` null), and the
  // footnote cards made here as the viewer reveals footnotes (`fn` = k,
  // keyed `fn:<k>`, holding the footnote's segment in `body`).
  const cards = [...railEl.querySelectorAll('.manuscript-card[data-mark]')].map((el) => ({
    n: Number(el.dataset.mark), fn: null, el, kind: `kind-${[...el.classList].find((c) => c.startsWith('kind-'))?.slice(5) || 'concept'}`,
    band: null, points: null, shadow: null, shape: null, link: null, ribbon: null, pinned: false, inline: false, slot: null, slotY: null,
  }));
  const markCards = () => cards.filter((card) => !card.fn);

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

  // ---- the view switch: the printed page keeps the reader's passage ----

  const viewLinks = [...root.querySelectorAll('.manuscript-view-link')];
  function syncViewLinks() {
    for (const link of viewLinks) {
      const target = (link.getAttribute('href') || '').split('#')[0];
      link.setAttribute('href', target + (/^#m\d+$/.test(location.hash) ? location.hash : ''));
    }
  }
  syncViewLinks();

  // ---- the two layouts ----
  //
  // Beside the text or, on a narrow screen, in it: the stylesheet's own
  // breakpoint, read here so the cards move between the rail and the text
  // as the screen crosses it.
  const narrowQuery = window.matchMedia('(max-width: 900px)');
  const narrow = () => narrowQuery.matches;

  // ---- the anchor join ----

  // Every anchor with the vertical extent of the line it sits on, in the
  // document's coordinates. An in-paragraph anchor is pinned at its
  // baseline (the viewer positions it absolutely); a stream anchor sits in
  // flow before its passage's first block or after its last, so its extent
  // is that block's edge, padded — a begin anchor's block is the next mount
  // (the anchor stands above the mount's margin), an end anchor's is the
  // previous, whose bottom edge the zero-size anchor already sits on.
  // A footnote's reference anchor is a begin side keyed `fn:<k>`.
  function measureAnchors() {
    const box = docEl.getBoundingClientRect();
    return [...docEl.querySelectorAll('.latex-anchor[data-mark], .latex-fnref[data-footnote]')].map((a) => {
      const r = a.getBoundingClientRect();
      const footnote = a.dataset.footnote !== undefined;
      const side = !footnote && a.dataset.side === 'e' ? 'e' : 'b';
      const inline = a.style.position === 'absolute';
      const x = r.left - box.left;
      let top = r.top - box.top;
      let bottom = top;
      if (inline) {
        top -= LINE_ABOVE;
        bottom += LINE_BELOW;
      } else if (side === 'b') {
        let next = a.nextElementSibling;
        while (next && (next.classList.contains('latex-anchor') || next.classList.contains('manuscript-card'))) next = next.nextElementSibling;
        if (next) top = next.getBoundingClientRect().top - box.top;
        top -= STREAM_PAD;
        bottom = top;
      } else {
        bottom += STREAM_PAD;
        top = bottom;
      }
      return { n: footnote ? `fn:${a.dataset.footnote}` : Number(a.dataset.mark), side, top, bottom, x, inline };
    });
  }

  // ---- footnotes as sidenotes ----

  // Whether the rail stands beside the text: above the breakpoint the
  // body's grid never stacks, it scrolls sideways where the two columns do
  // not fit (style.css), and a sidenote in a rail scrolled off the screen
  // is worse than an endnote; below it there is no rail (placeCards reads
  // `narrow()` first).
  let sidenotes = false;
  function railBesideText() {
    return reflowBody.scrollWidth <= reflowBody.clientWidth + 1;
  }

  const blocks = () => [...docEl.querySelectorAll('.latex-block')];
  const viewer = () => window.laxLatexViewer;

  function footnoteCard(k) {
    let card = cards.find((c) => c.fn === k);
    if (card) return card;
    let el;
    if (footnoteTemplate && footnoteTemplate.content) {
      el = footnoteTemplate.content.firstElementChild.cloneNode(true);
    } else {
      el = document.createElement('li');
      el.className = 'manuscript-card manuscript-footnote';
      el.append(Object.assign(document.createElement('div'), { className: 'manuscript-footnote-body' }));
    }
    el.dataset.footnote = String(k);
    el.id = `fn-${k}`;
    el.hidden = true;
    const body = el.querySelector('.manuscript-footnote-body') || el;
    card = {
      n: `fn:${k}`, fn: k, el, body, kind: 'kind-footnote',
      band: null, points: null, shadow: null, shape: null, link: null, ribbon: null, pinned: false,
    };
    el.addEventListener('mouseenter', () => noteHover(card, true));
    el.addEventListener('mouseleave', () => noteHover(card, false));
    el.addEventListener('click', (event) => {
      if (event.target.closest('a, button')) return;
      scrollToReference(card);
    });
    cards.push(card);
    railEl.append(el);
    return card;
  }

  // Lift every footnote segment the viewer has in the document into its
  // card. The viewer re-appends the segments to its root on every
  // re-layout and makes fresh ones on a font repaint (rerenderBlock), so
  // this runs, synchronously, on every reflow event; a segment already in
  // its card is not in the document and is left alone, a stale one is
  // replaced. The segment is moved, never copied: the viewer paints and
  // repaints it by reference (its own element, its own observer),
  // wherever it is mounted.
  function adoptFootnotes() {
    let moved = 0;
    for (const seg of docEl.querySelectorAll('.latex-footnote[data-footnote]')) {
      const k = Number(seg.dataset.footnote);
      if (!Number.isFinite(k) || k <= 0) continue;
      const card = footnoteCard(k);
      card.body.replaceChildren(seg);
      card.el.hidden = false;
      moved += 1;
    }
    // The viewer painted what was near the viewport before the move; a
    // segment that came from the end of the document is still empty or
    // stale, so ask again now that it sits beside its reference.
    const api = viewer();
    if (moved && api && api.paint) for (const block of blocks()) api.paint(block);
  }

  // Say whether the sidenotes are on, and at what measure, then let the
  // viewer re-lay out any block that needs it: a footnote segment is set at
  // the card's width while it is a sidenote and at the column's when it is
  // an endnote again, in which case the re-layout also returns it to the
  // document (the viewer re-mounts every segment). A block that changed
  // dispatches the reflow event, whose handler adopts and re-schedules.
  function settleFootnotes() {
    reflowBody.classList.toggle('manuscript-sidenotes', sidenotes);
    if (sidenotes) adoptFootnotes();
    const first = cards.find((card) => card.fn && !card.el.hidden);
    const measure = sidenotes && first ? first.body.clientWidth : 0;
    const api = viewer();
    for (const block of blocks()) {
      if (measure > 0) block.dataset.latexFootnoteWidth = String(measure);
      else delete block.dataset.latexFootnoteWidth;
      if (api && api.reflow) api.reflow(block);
    }
    if (!sidenotes) for (const card of cards) if (card.fn) card.el.hidden = true;
  }

  // The reference anchor carries a link to the sidenote — a small hit box
  // over the superscript the viewer painted before the anchor, outside the
  // SVG, so the text is untouched — for a pinned (in-paragraph) anchor
  // only; a stream anchor (\thanks) has nothing to sit over. The viewer
  // rebuilds its anchors on a font repaint, so this runs on every reflow.
  function linkReferences() {
    for (const anchor of docEl.querySelectorAll('.latex-fnref[data-footnote]')) {
      if (anchor.firstElementChild || anchor.style.position !== 'absolute') continue;
      const k = anchor.dataset.footnote;
      const link = document.createElement('a');
      link.className = 'latex-fnref-link';
      link.href = `#fn-${k}`;
      link.setAttribute('aria-label', `Footnote ${k}`);
      const card = () => cards.find((c) => c.fn === Number(k));
      link.addEventListener('mouseenter', () => { const c = card(); if (c) noteHover(c, true); });
      link.addEventListener('mouseleave', () => { const c = card(); if (c) noteHover(c, false); });
      link.addEventListener('focus', () => { const c = card(); if (c) noteHover(c, true); });
      link.addEventListener('blur', () => { const c = card(); if (c) noteHover(c, false); });
      link.addEventListener('click', (event) => {
        const c = card();
        if (!c) return;
        if (sidenotes && !c.el.hidden) {
          // The browser lands on the card (#fn-<k>, its :target outline);
          // a moment of the hover style says which one.
          noteFlash(c);
          return;
        }
        // The endnote is the segment itself, back in the document.
        const seg = docEl.querySelector(`.latex-footnote[data-footnote="${k}"]`);
        if (!seg) return;
        event.preventDefault();
        seg.scrollIntoView({ behavior: 'smooth', block: 'center' });
        seg.classList.add('latex-footnote-flash');
        setTimeout(() => seg.classList.remove('latex-footnote-flash'), 1200);
      });
      anchor.append(link);
    }
  }

  function referenceOf(card) {
    return docEl.querySelector(`.latex-fnref[data-footnote="${card.fn}"]`);
  }

  // Hovering (or focusing) either end lights both: the card and the
  // reference's hit box.
  function noteHover(card, hovering) {
    card.el.classList.toggle('manuscript-card-hover', hovering);
    const anchor = referenceOf(card);
    if (anchor) anchor.classList.toggle('latex-fnref-hover', hovering);
  }

  function noteFlash(card) {
    card.el.classList.add('manuscript-card-hover');
    setTimeout(() => card.el.classList.remove('manuscript-card-hover'), 1200);
  }

  function scrollToReference(card) {
    const anchor = referenceOf(card);
    if (!anchor) return;
    anchor.scrollIntoView({ behavior: 'smooth', block: 'center' });
    anchor.classList.add('latex-fnref-flash');
    setTimeout(() => anchor.classList.remove('latex-fnref-flash'), 1200);
  }

  // ---- placement ----

  function placeCards() {
    // The sidenotes first: they may ask the viewer for a re-layout, which
    // moves everything measured below.
    sidenotes = !narrow() && railBesideText();
    settleFootnotes();
    linkReferences();
    const active = cards.filter((card) => !card.fn || !card.el.hidden);
    if (!active.length) return;
    const byMark = bands(measureAnchors());
    for (const card of cards) card.band = byMark[card.n] || null;
    if (narrow()) {
      // A card that moved changed the text's height; the viewer re-pins the
      // anchors below it and announces a reflow, which paints — painting
      // now would draw the passages where they were.
      if (placeInline()) return;
    } else {
      placeRail(active, byMark);
    }
    paintHighlights();
    drawLinks();
  }

  // A card's height with its body closed: the room it takes in the rail
  // unless pinned. A card opening under the pointer lies over the cards
  // below it (the stylesheet raises it) rather than shoving them down.
  function closedHeight(card) {
    const body = card.el.querySelector('.manuscript-card-body');
    if (!body || body.hidden) return card.el.offsetHeight;
    return card.el.offsetHeight - body.offsetHeight - parseFloat(getComputedStyle(body).marginTop || '0');
  }

  // Beside the text: every card in the rail, stacked by its passage —
  // `active` being the mark cards and the footnote cards showing.
  function placeRail(active, byMark) {
    if (cards.some((card) => card.inline)) {
      for (const card of cards) leaveText(card);
      railEl.append(...cards.map((card) => card.el));
    }
    const bodyBox = reflowBody.getBoundingClientRect();
    const docTop = docEl.getBoundingClientRect().top - bodyBox.top;
    const railTop = railEl.getBoundingClientRect().top - bodyBox.top;
    railEl.classList.add('manuscript-rail-live');
    // The rail in document order (the DOM too, when it moved).
    const order = railOrder(active, byMark);
    const sorted = order.map((index) => active[index]);
    if (sorted.some((card, index) => card !== active[index])) {
      const others = cards.filter((card) => !active.includes(card));
      cards.length = 0;
      cards.push(...sorted, ...others);
      railEl.append(...sorted.map((card) => card.el));
    }
    const result = place(sorted.map((card) => ({ n: card.n, height: card.pinned ? card.el.offsetHeight : closedHeight(card) })), byMark, CARD_GAP, railTop - docTop);
    let bottom = 0;
    sorted.forEach((card, index) => {
      card.el.style.top = `${result.tops[index]}px`;
      card.el.classList.toggle('manuscript-card-unplaced', !result.placed[index]);
      bottom = Math.max(bottom, result.tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(docEl.offsetHeight, bottom + 24)}px`;
  }

  // In the text: a pinned card sits in its slot — under the run of text
  // the reader tapped, or under the passage's first run for a deep link
  // (a proof can run for pages; the card belongs where the reader is) —
  // and failing a slot, after the passage's end anchor, which the viewer
  // keeps after the segment holding the passage's last line. Cards of one
  // passage stack in mark order. The others wait in the rail, which the
  // stylesheet hides. The viewer rebuilds its tree on every re-layout,
  // dropping the card, so this runs on every reflow and is a no-op when
  // the card is already where it belongs. Returns whether the text
  // changed.
  function placeInline() {
    railEl.style.height = '';
    let changed = false;
    for (const card of markCards()) {
      card.el.classList.toggle('manuscript-card-unplaced', !card.band);
      changed = (card.pinned ? enterText(card) : leaveText(card)) || changed;
    }
    return changed;
  }

  // The viewer's segments — the runs of paragraphs and the displays, one
  // element each in a block's root — are what a card can follow.
  const isMount = (el) => !el.classList.contains('latex-anchor') && !el.classList.contains('manuscript-card');
  function mountsOf(block) {
    const root = block.firstElementChild;
    return root ? [...root.children].filter(isMount) : [];
  }

  // The slot under the text at `y` (the document's coordinates): the
  // segment there, or the last one above it, as {block, mount} indices —
  // stable across the viewer's reflows, which never re-segment.
  function slotAtY(y) {
    if (!Number.isFinite(y)) return null;
    const docTop = docEl.getBoundingClientRect().top;
    const blocks = [...docEl.querySelectorAll('.latex-block')];
    for (let b = 0; b < blocks.length; b++) {
      const box = blocks[b].getBoundingClientRect();
      if (y < box.top - docTop || y > box.bottom - docTop) continue;
      const mounts = mountsOf(blocks[b]);
      let slot = null;
      mounts.forEach((mount, m) => { if (mount.getBoundingClientRect().top - docTop <= y) slot = { block: b, mount: m }; });
      return slot;
    }
    return null;
  }

  function slotElement(slot) {
    if (!slot) return null;
    const block = docEl.querySelectorAll('.latex-block')[slot.block];
    return block ? mountsOf(block)[slot.mount] || null : null;
  }

  function endAnchor(card) {
    return docEl.querySelector(`.latex-anchor[data-mark="${card.n}"][data-side="e"]`)
      || docEl.querySelector(`.latex-anchor[data-mark="${card.n}"][data-side="b"]`);
  }

  function enterText(card) {
    // The slot resolves once the text has the passage — a deep link pins
    // its card before the viewer has laid anything out — and then holds.
    if (!card.slot) card.slot = slotAtY(card.slotY !== null ? card.slotY : card.band ? card.band.top + LINE_ABOVE + 2 : NaN);
    // A passage the text does not locate: the card heads the paper, with
    // its note saying so.
    let ref = slotElement(card.slot) || endAnchor(card);
    let next = ref ? ref.nextElementSibling : docEl.firstElementChild;
    // Past the anchors closing passages here (an end anchor sits on its
    // segment's bottom edge, and a card before it would stretch its
    // passage), and the cards of the same slot before this one.
    for (;;) {
      if (!next || next === card.el) break;
      if (next.classList.contains('latex-anchor')) {
        if (next.dataset.side !== 'e' && next.style.position !== 'absolute') break;
      } else if (!next.classList.contains('manuscript-card') || Number(next.dataset.mark) > card.n) break;
      ref = next;
      next = next.nextElementSibling;
    }
    if (next === card.el && card.inline) return false;
    if (ref) ref.after(card.el);
    else docEl.prepend(card.el);
    card.inline = true;
    card.el.style.top = '';
    card.el.classList.add('manuscript-card-inline');
    return true;
  }

  function leaveText(card) {
    if (!card.inline) return false;
    card.inline = false;
    card.el.classList.remove('manuscript-card-inline');
    const before = [...railEl.children].find((el) => Number(el.dataset.mark) > card.n);
    if (before) railEl.insertBefore(card.el, before);
    else railEl.append(card.el);
    return true;
  }

  // Per passage: its flat region along the text, and behind it a lighter
  // shadow a fixed margin beyond the column on both sides, from the
  // passage's first line to its last. The gutter band starts at the
  // shadow's right edge. Coordinates are the document's. A sidenote has
  // no passage: nothing is painted for it.
  function paintHighlights() {
    const width = docEl.clientWidth;
    hlEl.setAttribute('viewBox', `0 0 ${width} ${docEl.clientHeight}`);
    for (const card of markCards()) {
      if (!card.band) {
        if (card.shape) { card.shape.remove(); card.shape = null; }
        if (card.shadow) { card.shadow.remove(); card.shadow = null; }
        card.points = null;
        continue;
      }
      card.points = outline(card.band, width);
      if (!card.shape) {
        card.shape = svgNode('path', { class: `manuscript-hl ${card.kind}`, 'data-mark': card.n });
        shapesEl.append(card.shape);
      }
      card.shape.setAttribute('d', `M${card.points.map(([x, y]) => `${x.toFixed(1)},${y.toFixed(1)}`).join('L')}Z`);
      if (!card.shadow) {
        card.shadow = svgNode('rect', { class: `manuscript-hl-shadow ${card.kind}`, 'data-mark': card.n });
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
  // without a seam. Nothing to draw where the cards are in the text.
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
    for (const card of markCards()) {
      if (!card.band || narrow()) {
        if (card.link) { card.link.remove(); card.link = null; }
        card.ribbon = null;
        continue;
      }
      const top = docTop + card.band.top;
      const bottom = docTop + card.band.bottom;
      const ct = railEl.offsetTop + card.el.offsetTop;
      const cb = ct + card.el.offsetHeight;
      const d = `M${xl},${top.toFixed(1)} C${xm},${top.toFixed(1)} ${xm},${ct} ${xr},${ct} L${xr},${cb} C${xm},${cb} ${xm},${bottom.toFixed(1)} ${xl},${bottom.toFixed(1)} Z`;
      if (!card.link) {
        card.link = svgNode('path', { class: `manuscript-link ${card.kind}`, 'data-mark': card.n });
        linksEl.append(card.link);
      }
      card.link.setAttribute('d', d);
      // The ribbon's geometry, for hit-testing: the band across the gutter.
      card.ribbon = { xl, xm, xr, top, bottom, ct, cb };
    }
  }

  // Whether (x, y), in the reflow body's coordinates, lies inside the
  // gutter band, whose edges are the cubic curves drawLinks draws (the PDF
  // surface's test, manuscript.js).
  function ribbonContains(band, x, y) {
    if (x < band.xl || x > band.xr) return false;
    const bez = (a, b, c, d, t) => a * (1 - t) ** 3 + 3 * b * t * (1 - t) ** 2 + 3 * c * t * t * (1 - t) + d * t ** 3;
    let lo = 0;
    let hi = 1;
    for (let i = 0; i < 24; i++) {
      const mid = (lo + hi) / 2;
      if (bez(band.xl, band.xm, band.xm, band.xr, mid) < x) lo = mid; else hi = mid;
    }
    const t = (lo + hi) / 2;
    return y >= bez(band.top, band.top, band.ct, band.ct, t) && y <= bez(band.bottom, band.bottom, band.cb, band.cb, t);
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

  // `y`, in the document's coordinates, is where the card should open in
  // the text; without one it opens under the passage's first line.
  function setPinned(card, pinned, y) {
    card.pinned = pinned;
    card.slot = null;
    card.slotY = pinned && Number.isFinite(y) ? y : null;
    card.el.classList.toggle('manuscript-card-pinned', pinned);
    if (isExpanded(card) !== pinned) setExpanded(card, pinned);
    else if (narrow()) placeCards();
  }

  // The cards of one passage: in the text, a tap on a theorem marked for
  // three concepts opens all three (there is no rail to reach the others
  // from); in the rail each card is its own.
  function passageCards(card) {
    if (!narrow() || !card.band) return [card];
    return markCards().filter((other) => other === card || (other.band
      && Math.abs(other.band.top - card.band.top) < SAME_BAND
      && Math.abs(other.band.bottom - card.band.bottom) < SAME_BAND));
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

  for (const card of markCards()) {
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (toggle) toggle.addEventListener('click', (event) => {
      event.stopPropagation();
      setPinned(card, !card.pinned);
    });
    card.el.addEventListener('click', (event) => {
      if (event.target.closest('a, button')) return;
      // In the text the card is under its passage already: a tap on the
      // head closes it, and the body is for reading.
      if (card.inline) {
        if (event.target.closest('.manuscript-card-head')) setPinned(card, false);
        return;
      }
      setPinned(card, !card.pinned);
      scrollToPassage(card);
    });
  }

  // ---- the passages: hover opens their cards, click pins ----
  //
  // The highlight layer takes no pointer events so the text under it stays
  // selectable; hovers and clicks are hit-tested here against the regions
  // (the innermost passage winning), then the shadows (the shortest), then
  // the ribbons across the gutter (the one drawn in front). The footnote
  // cards and their reference links keep their own hover (noteHover).
  function cardAt(event) {
    if (event.target.closest('.manuscript-rail, .manuscript-card, a')) return null;
    const best = cardAtPassage(event);
    return best || cardAtRibbon(event);
  }

  function cardAtRibbon(event) {
    if (!linksEl) return null;
    const box = reflowBody.getBoundingClientRect();
    const x = event.clientX - box.left + reflowBody.scrollLeft;
    const y = event.clientY - box.top + reflowBody.scrollTop;
    let best = null;
    let bestOrder = -1;
    for (const card of markCards()) {
      if (!card.ribbon || !card.link || !ribbonContains(card.ribbon, x, y)) continue;
      const order = Array.prototype.indexOf.call(linksEl.children, card.link);
      if (order > bestOrder) { best = card; bestOrder = order; }
    }
    return best;
  }

  function cardAtPassage(event) {
    const box = docEl.getBoundingClientRect();
    const x = event.clientX - box.left;
    const y = event.clientY - box.top;
    let best = null;
    let bestSpan = Infinity;
    for (const card of markCards()) {
      if (!card.points || !contains(card.points, x, y)) continue;
      const span = card.band.bottom - card.band.top;
      if (span < bestSpan) { best = card; bestSpan = span; }
    }
    if (best) return best;
    const width = docEl.clientWidth;
    if (x < -SHADOW_MARGIN || x > width + SHADOW_MARGIN) return null;
    for (const card of markCards()) {
      if (!card.band || y < card.band.top || y > card.band.bottom) continue;
      const span = card.band.bottom - card.band.top;
      if (span < bestSpan) { best = card; bestSpan = span; }
    }
    return best;
  }
  // One hover: a card stays open while the pointer is on the card, its
  // passage, or the ribbon between them, and moving from one to another
  // never closes it in between (closing would shrink the ribbon under the
  // pointer) — the PDF surface's rule. No hover in the text: a touch
  // screen's tap would open on the move and close on the click.
  let hovered = null;
  function hover(card) {
    if (card === hovered) return;
    if (hovered) { setHover(hovered, false); hovered.el.classList.remove('manuscript-card-hover'); }
    hovered = card;
    if (hovered) { setHover(hovered, true); hovered.el.classList.add('manuscript-card-hover'); }
  }
  function cardInRail(event) {
    const el = event.target.closest('.manuscript-card');
    return el ? cards.find((card) => card.el === el && !card.fn) || null : null;
  }
  reflowBody.addEventListener('mousemove', (event) => {
    if (narrow()) return;
    hover(cardInRail(event) || cardAt(event));
  });
  reflowBody.addEventListener('mouseleave', () => hover(null));
  reflowBody.addEventListener('click', (event) => {
    if (event.target.closest('.manuscript-rail, .manuscript-card')) return;
    const best = cardAt(event);
    if (!best) return;
    const pinned = !best.pinned;
    const y = event.clientY - docEl.getBoundingClientRect().top;
    for (const card of passageCards(best)) setPinned(card, pinned, y);
    flash(best);
    // Brings the card into view: where the rail is scrolled off to the
    // side, or where it opened under a passage longer than the screen.
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

  // A re-layout has just re-mounted every segment in the document: take
  // the footnotes back into their cards before the frame paints, then
  // re-place everything.
  document.addEventListener('latex-viewer:reflow', () => {
    if (sidenotes) adoptFootnotes();
    schedule();
  });
  window.addEventListener('resize', schedule);
  const onNarrowChange = () => { hover(null); schedule(); };
  if (narrowQuery.addEventListener) narrowQuery.addEventListener('change', onNarrowChange);
  else narrowQuery.addListener(onNarrowChange);
  window.addEventListener('hashchange', () => { hashPinned = false; syncViewLinks(); honourHash(); });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(schedule);
})();
