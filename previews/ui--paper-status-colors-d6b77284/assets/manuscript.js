// The paper viewer: renders the PDF with pdf.js page by page as they scroll
// into view, paints one highlight region per marked passage from the page's
// text items (never from the text-layer DOM), places the pre-rendered cards
// in the rail beside their passages, and draws a band across the gutter
// from each passage to its card. Geometry comes from manuscript-place.js
// and manuscript-regions.js;
// this file is the DOM and pdf.js glue.
//
// Runs under the page CSP: pdf.js and its worker are same-origin files
// named in the data attributes, and the PDF is fetched from the same origin.
(() => {
  const root = document.querySelector('.manuscript[data-pdf]');
  const place = window.laxManuscript;
  const regions = window.laxManuscriptRegions;
  if (!root || !place || !regions) return;
  const pagesEl = document.getElementById('manuscript-pages');
  const railEl = document.getElementById('manuscript-rail');
  const linksEl = document.getElementById('manuscript-links');
  const bodyEl = pagesEl && pagesEl.parentElement;
  const statusEl = document.getElementById('manuscript-status');
  const dataEl = document.getElementById('manuscript-data');
  if (!pagesEl || !railEl || !dataEl || !linksEl) return;

  const data = JSON.parse(dataEl.textContent || '{}');
  const marks = Array.isArray(data.marks) ? data.marks : [];
  const RENDER_MARGIN = '900px';
  const CARD_GAP = 8;
  const SVG = 'http://www.w3.org/2000/svg';

  const pageEls = [...pagesEl.querySelectorAll('.manuscript-page')];
  const cards = marks.map((mark) => {
    const el = railEl.querySelector(`.manuscript-card[data-mark="${mark.n}"]`);
    const colorClasses = el ? [...el.classList].filter((name) => name.startsWith('kind-') || name === 'line-proven' || name === 'line-open').join(' ') : '';
    return { mark, el, colorClasses, hits: [], rects: [], bands: [], probes: [], probeShape: null, want: 0, resolved: null, link: null, pinned: false, hovering: false, paintOrder: 0 };
  }).filter((card) => card.el);
  let paintOrder = 0;

  // The switch to the reflowed page keeps the reader's passage: its link
  // carries the `#m<n>` fragment along.
  const viewLinks = [...root.querySelectorAll('.manuscript-view-link')];
  const syncViewLinks = () => {
    for (const link of viewLinks) {
      const target = (link.getAttribute('href') || '').split('#')[0];
      link.setAttribute('href', target + (/^#m\d+$/.test(location.hash) ? location.hash : ''));
    }
  };
  syncViewLinks();
  window.addEventListener('hashchange', syncViewLinks);

  const setStatus = (text, failed = false) => {
    if (!statusEl) return;
    statusEl.textContent = text;
    statusEl.classList.toggle('manuscript-status-failed', failed);
  };

  // ---- pdf.js ----

  let pdfjs;
  let doc;
  const pageState = []; // per page: { page, viewport, text, analysed, rendered, task, el }
  let scale = 1;

  async function loadDocument() {
    pdfjs = await import(root.dataset.pdfjs);
    pdfjs.GlobalWorkerOptions.workerSrc = new URL(root.dataset.pdfjsWorker, location.href).href;
    const url = new URL(root.dataset.pdf, location.href).href;
    doc = await pdfjs.getDocument({ url, isEvalSupported: false }).promise;
    for (let p = 1; p <= doc.numPages; p++) {
      const el = pageEls[p - 1];
      if (!el) break;
      pageState.push({ number: p, page: null, viewport: null, text: null, analysed: null, rendered: false, task: null, el });
    }
  }

  async function pdfPage(state) {
    if (!state.page) state.page = await doc.getPage(state.number);
    return state.page;
  }

  async function pageText(state) {
    if (!state.text) {
      const page = await pdfPage(state);
      state.text = await readTextContent(page);
      state.analysed = place.analyzePage(place.textItems(state.text));
    }
    return state.text;
  }

  // pdf.js's own getTextContent drains the text stream with `for await`,
  // which WebKit cannot do (ReadableStream has no async iterator there, so
  // mobile Safari failed before the first page); a reader reads the same
  // stream everywhere.
  async function readTextContent(page) {
    const reader = page.streamTextContent().getReader();
    const text = { items: [], styles: Object.create(null), lang: null };
    for (;;) {
      const { value, done } = await reader.read();
      if (done) return text;
      if (text.lang == null && value.lang != null) text.lang = value.lang;
      Object.assign(text.styles, value.styles);
      text.items.push(...value.items);
    }
  }

  function currentScale() {
    const width = pagesEl.clientWidth;
    const first = data.pageSizes && data.pageSizes[0];
    const pageWidth = first ? first[0] : 595.28;
    return width > 0 ? width / pageWidth : 1;
  }

  async function viewportOf(state) {
    const page = await pdfPage(state);
    if (!state.viewport || state.viewport.scale !== scale) state.viewport = page.getViewport({ scale });
    return state.viewport;
  }

  // ---- rendering (lazy) ----

  async function renderPage(state) {
    if (state.rendered || state.task) return;
    const page = await pdfPage(state);
    const viewport = await viewportOf(state);
    const dpr = window.devicePixelRatio || 1;
    const canvas = document.createElement('canvas');
    canvas.width = Math.floor(viewport.width * dpr);
    canvas.height = Math.floor(viewport.height * dpr);
    canvas.style.width = `${viewport.width}px`;
    canvas.style.height = `${viewport.height}px`;
    const context = canvas.getContext('2d');
    const task = page.render({ canvas, canvasContext: context, viewport, transform: dpr === 1 ? null : [dpr, 0, 0, dpr, 0, 0] });
    state.task = task;
    try {
      await task.promise;
    } catch (error) {
      state.task = null;
      if (error && error.name === 'RenderingCancelledException') return;
      throw error;
    }
    state.task = null;
    if (state.viewport !== viewport) return; // a resize won while rendering
    const text = await pageText(state);
    const textLayerEl = document.createElement('div');
    textLayerEl.className = 'textLayer';
    const textLayer = new pdfjs.TextLayer({ textContentSource: text, container: textLayerEl, viewport });
    await textLayer.render();
    state.el.style.setProperty('--scale-factor', String(scale));
    state.el.style.setProperty('--total-scale-factor', String(scale));
    state.el.prepend(textLayerEl);
    state.el.prepend(canvas);
    state.el.classList.add('manuscript-page-rendered');
    state.rendered = true;
  }

  function clearPage(state) {
    if (state.task) { state.task.cancel(); state.task = null; }
    state.el.replaceChildren();
    state.el.classList.remove('manuscript-page-rendered');
    state.rendered = false;
  }

  const observer = 'IntersectionObserver' in window
    ? new IntersectionObserver((entries) => {
        for (const entry of entries) {
          if (!entry.isIntersecting) continue;
          const state = pageState[Number(entry.target.dataset.page) - 1];
          if (state) renderPage(state).catch((error) => console.error('page render failed', error));
        }
      }, { rootMargin: RENDER_MARGIN })
    : null;

  // ---- highlights and cards ----

  async function resolveMarks() {
    const needed = new Set();
    for (const { mark } of cards) {
      for (let p = mark.begin.page - 1; p <= mark.end.page + 1; p++) if (p >= 1 && p <= pageState.length) needed.add(p);
    }
    for (const p of [...needed].sort((a, b) => a - b)) await pageText(pageState[p - 1]);
    const analysed = pageState.map((state) => state.analysed);
    for (const card of cards) {
      card.resolved = place.resolveRange(card.mark, analysed);
      if (!card.resolved) card.el.classList.add('manuscript-card-unplaced');
    }
  }

  function svgNode(name, attrs) {
    const node = document.createElementNS(SVG, name);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
    return node;
  }

  async function paintHighlights() {
    const outlines = [];
    for (const card of cards) {
      card.rects = [];
      if (!card.resolved) continue;
      const segments = card.resolved.segments;
      for (const seg of segments) {
        const state = pageState[seg.page - 1];
        const viewport = await viewportOf(state);
        const pageRight = Math.max(...state.analysed.blocks.map((block) => block.x1));
        for (const shape of place.segmentShapes(state.analysed, seg)) {
          outlines.push({ card, group: seg.page,
            points: shape.points.map(([x, y]) => viewport.convertToViewportPoint(x, y)),
            left: viewport.convertToViewportPoint(shape.columnLeft, 0)[0],
            right: viewport.convertToViewportPoint(shape.columnRight, 0)[0],
            singleLine: shape.points.length === 4,
            connects: shape.columnRight >= pageRight - 1 });
        }
      }
    }
    regions.prepare(outlines).forEach((points, i) => {
      if (!points.length) return;
      const { card, group: page, right: margin, connects, singleLine } = outlines[i];
      const left = Math.min(...points.map((point) => point[0]));
      const right = Math.max(...points.map((point) => point[0]));
      const top = Math.min(...points.map((point) => point[1]));
      const bottom = Math.max(...points.map((point) => point[1]));
      card.rects.push({ page, left, top, width: right - left, height: bottom - top, points, margin, connects, singleLine });
    });
  }

  async function placeCards() {
    for (const card of cards) {
      const first = card.rects[0];
      const point = card.mark.begin;
      const state = pageState[(first ? first.page : point.page) - 1];
      if (!state) continue;
      let y;
      if (first) y = first.top;
      else {
        const viewport = await viewportOf(state);
        y = viewport.convertToViewportPoint(point.x, point.y)[1];
      }
      card.want = state.el.offsetTop + y - 4;
    }
    stack();
  }

  // A card's height with its body closed: the room it takes in the rail
  // unless pinned. A card opening under the pointer lies over the cards
  // below it (the stylesheet raises it) rather than shoving them down.
  function closedHeight(card) {
    const body = card.el.querySelector('.manuscript-card-body');
    if (!body || body.hidden) return card.el.offsetHeight;
    return card.el.offsetHeight - body.offsetHeight - parseFloat(getComputedStyle(body).marginTop || '0');
  }

  // The rail is always beside the pages (the body scrolls sideways where
  // the screen is narrower than the two together), so cards sit at their
  // passages' y from the first layout on.
  function stack() {
    railEl.classList.add('manuscript-rail-live');
    const tops = place.stackCards(cards.map((card) => ({ want: card.want, height: card.pinned ? card.el.offsetHeight : closedHeight(card) })), CARD_GAP);
    let bottom = 0;
    cards.forEach((card, index) => {
      card.el.style.top = `${tops[index]}px`;
      bottom = Math.max(bottom, tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(pagesEl.offsetHeight, bottom + 24)}px`;
    orderRail(tops);
    drawLinks();
  }

  // The rail's elements in the order the cards show: the marks come in the
  // record's order, so without this the tab order (and a screen reader's)
  // would jump about the pages.
  function orderRail(tops) {
    const sorted = cards.map((card, index) => ({ card, top: tops[index], index }))
      .sort((a, b) => a.top - b.top || a.index - b.index)
      .map(({ card }) => card.el);
    if (sorted.every((el, i) => railEl.children[i] === el)) return;
    railEl.append(...sorted);
  }

  // Passage and gutter are one rounded path in a common overlay. Only a
  // region touching the last column's right edge can continue to the rail.
  function drawLinks() {
    if (!linksEl || !bodyEl) return;
    const width = bodyEl.clientWidth;
    const height = bodyEl.clientHeight;
    linksEl.setAttribute('viewBox', `0 0 ${width} ${height}`);
    linksEl.classList.add('manuscript-links-live');
    const bodyBox = bodyEl.getBoundingClientRect();
    for (const card of cards) {
      card.bands = [];
      card.probes = [];
      if (!card.rects.length) {
        if (card.link) { card.link.remove(); card.link = null; }
        if (card.probeShape) { card.probeShape.remove(); card.probeShape = null; }
        card.hits = [];
        continue;
      }
      const box = card.el.getBoundingClientRect();
      const xr = box.left - bodyBox.left + bodyEl.scrollLeft + 2;
      const ct = box.top - bodyBox.top + bodyEl.scrollTop;
      const cb = ct + box.height;
      const head = card.el.querySelector('.manuscript-card-head').getBoundingClientRect();
      const cy = (head.top + head.bottom) / 2 - bodyBox.top + bodyEl.scrollTop;
      const d = card.rects.map((rect) => {
        const page = pageState[rect.page - 1].el;
        const pageBox = page.getBoundingClientRect();
        const x = pageBox.left - bodyBox.left + bodyEl.scrollLeft + page.clientLeft;
        const y = pageBox.top - bodyBox.top + bodyEl.scrollTop + page.clientTop;
        const points = rect.points.map(([px, py]) => [x + px, y + py]);
        const edge = rect.connects ? regions.rightEdge(points, x + rect.margin) : null;
        const band = edge && { ...edge, xr, xm: (edge.xl + xr) / 2, ct, cb };
        if (band) card.bands.push(band);
        else if (rect.connects && rect.singleLine) {
          const probe = regions.probe(points, x + rect.margin, xr, cy, y + rect.top);
          if (probe) card.probes.push(probe);
        }
        return regions.path(points, band);
      }).join('');
      if (!card.link) {
        card.link = svgNode('path', { class: `manuscript-hl ${card.colorClasses}`, 'data-mark': card.mark.n });
        linksEl.append(card.link);
      }
      card.link.setAttribute('d', d);
      if (card.probes.length) {
        if (!card.probeShape) {
          card.probeShape = svgNode('path', { class: `manuscript-probe ${card.colorClasses}`, 'data-mark': card.mark.n });
          linksEl.append(card.probeShape);
        }
        card.probeShape.setAttribute('d', card.probes.map((probe) => probe.path).join(''));
      } else if (card.probeShape) { card.probeShape.remove(); card.probeShape = null; }
      card.hits = [card.link, card.probeShape].filter(Boolean);
    }
    syncHighlights();
  }

  // Whether (x, y), in the body's coordinates, lies on a card's gutter band.
  function ribbonContains(band, x, y) {
    if (x < band.xl || x > band.xr) return false;
    // x(t) is monotone in t, so bisect for the t under the pointer.
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

  // A hover raises a card within its tier; pinned regions always win.
  function raise(card) {
    card.paintOrder = ++paintOrder;
    syncHighlights();
  }

  function syncHighlights() {
    const compare = (a, b) => Number(a.pinned) - Number(b.pinned)
      || Number(a.hovering) - Number(b.hovering) || a.paintOrder - b.paintOrder;
    const ordered = [...cards].sort(compare);
    for (const card of ordered) {
      for (const hit of card.hits) {
        hit.classList.toggle('manuscript-hl-active', isExpanded(card));
        hit.classList.toggle('manuscript-hl-hover', card.hovering);
        hit.classList.toggle('manuscript-hl-pinned', card.pinned);
      }
    }
    const links = ordered.flatMap((card) => card.hits);
    if (linksEl && links.some((node, i) => linksEl.children[i] !== node)) linksEl.append(...links);
  }

  function setExpanded(card, expanded) {
    card.el.classList.toggle('manuscript-card-expanded', expanded);
    const body = card.el.querySelector('.manuscript-card-body');
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (body) body.hidden = !expanded;
    if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
    stack();
    if (expanded) raise(card);
  }

  // A card opens while hovered — from the rail or from its passage — and
  // stays open once pinned by a click.
  function setHover(card, hovering) {
    card.hovering = hovering;
    if (hovering) raise(card);
    if (!card.pinned && isExpanded(card) !== hovering) setExpanded(card, hovering);
    else syncHighlights();
  }

  function setPinned(card, pinned) {
    card.pinned = pinned;
    card.el.classList.toggle('manuscript-card-pinned', pinned);
    if (isExpanded(card) !== pinned) setExpanded(card, pinned);
    syncHighlights();
  }

  function isExpanded(card) {
    return card.el.classList.contains('manuscript-card-expanded');
  }

  function scrollToPassage(card) {
    const first = card.rects[0];
    const target = pageState[(first ? first.page : card.mark.begin.page) - 1]?.el;
    if (!target) return;
    const box = target.getBoundingClientRect();
    const header = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--header-height')) || 0;
    window.scrollTo({ top: window.scrollY + box.top + (first ? first.top : 0) - header * 16 - 120, behavior: 'smooth' });
    flash(card);
  }

  function flash(card) {
    for (const hit of card.hits) hit.classList.add('manuscript-hl-flash');
    setTimeout(() => { for (const hit of card.hits) hit.classList.remove('manuscript-hl-flash'); }, 1200);
  }

  function wireCards() {
    for (const card of cards) {
      const toggle = card.el.querySelector('.manuscript-card-toggle');
      if (toggle) toggle.addEventListener('click', (event) => {
        event.stopPropagation();
        setPinned(card, !card.pinned);
      });
      card.el.addEventListener('click', (event) => {
        if (event.target.closest('a, button')) return;
        if (event.clientY > card.el.querySelector('.manuscript-card-head').getBoundingClientRect().bottom) return;
        setPinned(card, !card.pinned);
        scrollToPassage(card);
      });
    }
    // Highlights take no pointer events so the text under them stays
    // selectable; clicks and hovers are hit-tested here, the innermost
    // passage winning.
    const cardAt = (event) => {
      const pageEl = event.target.closest('.manuscript-page');
      if (!pageEl || event.target.closest('a')) return null;
      const pageNumber = Number(pageEl.dataset.page);
      const box = pageEl.getBoundingClientRect();
      const x = event.clientX - box.left - pageEl.clientLeft;
      const y = event.clientY - box.top - pageEl.clientTop;
      let best = null;
      let bestArea = Infinity;
      for (const card of cards) {
        for (const rect of card.rects) {
          if (rect.page !== pageNumber) continue;
          if (x < rect.left || x > rect.left + rect.width || y < rect.top || y > rect.top + rect.height) continue;
          if (!regions.contains(rect.points, x, y)) continue;
          const area = card.rects.reduce((sum, r) => sum + r.width * r.height, 0);
          if (area < bestArea) { best = card; bestArea = area; }
        }
      }
      return best;
    };
    // The gutter band is a target too, with the one drawn in front winning.
    const cardAtRibbon = (event) => {
      if (!bodyEl || !linksEl || event.target.closest('.manuscript-rail, a')) return null;
      const box = bodyEl.getBoundingClientRect();
      const x = event.clientX - box.left + bodyEl.scrollLeft;
      const y = event.clientY - box.top + bodyEl.scrollTop;
      let best = null;
      let bestOrder = -1;
      for (const card of cards) {
        if (!card.link || !card.bands.some((band) => ribbonContains(band, x, y))
          && !card.probes.some((probe) => regions.probeContains(probe, x, y))) continue;
        const order = Array.prototype.indexOf.call(linksEl.children, card.link);
        if (order > bestOrder) { best = card; bestOrder = order; }
      }
      return best;
    };
    // The card in the rail is the target on its own element.
    const cardInRail = (event) => {
      const el = event.target.closest('.manuscript-card');
      const head = el?.querySelector('.manuscript-card-head');
      if (!head || event.clientY > head.getBoundingClientRect().bottom) return null;
      return el ? cards.find((card) => card.el === el) || null : null;
    };
    // One hover: a card stays open while the pointer is on its first line, its
    // passage, or the ribbon between them, and moving from one to another
    // never closes it in between — closing would shrink the ribbon under
    // the pointer. Tested where the pointer is on every move, and the
    // hovered card is only ever swapped, never dropped and re-found.
    const hoverSurface = bodyEl || pagesEl;
    let hovered = null;
    const hover = (card) => {
      if (card === hovered) return;
      if (hovered) { setHover(hovered, false); hovered.el.classList.remove('manuscript-card-hover'); }
      hovered = card;
      if (hovered) { setHover(hovered, true); hovered.el.classList.add('manuscript-card-hover'); }
    };
    hoverSurface.addEventListener('mousemove', (event) => {
      hover(cardInRail(event) || cardAt(event) || cardAtRibbon(event));
    });
    hoverSurface.addEventListener('mouseleave', () => hover(null));
    hoverSurface.addEventListener('click', (event) => {
      if (event.target.closest('.manuscript-rail')) return;
      const best = cardAt(event) || cardAtRibbon(event);
      if (!best) return;
      const pinned = !best.pinned;
      setPinned(best, pinned);
      flash(best);
      // Brings the card into view where the rail is scrolled off to the side.
      if (pinned) best.el.scrollIntoView({ behavior: 'smooth', block: 'nearest', inline: 'nearest' });
    });
  }

  function openFromHash() {
    const match = /^#m(\d+)$/.exec(location.hash);
    if (!match) return;
    const card = cards.find((c) => c.mark.n === Number(match[1]));
    if (!card) return;
    setPinned(card, true);
    scrollToPassage(card);
  }

  // ---- layout ----

  let layoutRunning = false;
  let layoutAgain = false;
  async function layout() {
    if (layoutRunning) { layoutAgain = true; return; }
    layoutRunning = true;
    try {
      scale = currentScale();
      for (const state of pageState) {
        clearPage(state);
        state.viewport = null;
      }
      await paintHighlights();
      await placeCards();
      // Re-observing an element already observed changes nothing, so a
      // relayout drops and re-adds every page to get the initial callback.
      if (observer) for (const state of pageState) { observer.unobserve(state.el); observer.observe(state.el); }
      else for (const state of pageState) await renderPage(state);
    } finally {
      layoutRunning = false;
      if (layoutAgain) { layoutAgain = false; layout(); }
    }
  }

  let lastWidth = pagesEl.clientWidth;
  const onResize = () => {
    const width = pagesEl.clientWidth;
    if (Math.abs(width - lastWidth) < 2) { stack(); return; }
    lastWidth = width;
    layout().catch((error) => console.error('paper layout failed', error));
  };

  async function main() {
    await loadDocument();
    await resolveMarks();
    wireCards();
    await layout();
    const located = cards.filter((card) => card.resolved).length;
    setStatus(`${doc.numPages} page${doc.numPages === 1 ? '' : 's'} · ${located} of ${cards.length} passages located`);
    root.classList.add('manuscript-ready');
    openFromHash();
    window.addEventListener('hashchange', openFromHash);
    window.addEventListener('resize', onResize);
    if ('ResizeObserver' in window) new ResizeObserver(onResize).observe(pagesEl);
    document.fonts?.ready.then(() => stack());
  }

  const start = () => main().catch((error) => {
    console.error('paper viewer failed', error);
    setStatus(`The paper could not be shown here (${error && error.message ? error.message : error}). Download the PDF instead.`, true);
    root.classList.add('manuscript-failed');
  });
  start();
})();
