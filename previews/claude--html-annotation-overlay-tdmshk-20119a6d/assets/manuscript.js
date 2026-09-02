// The paper viewer: renders the PDF with pdf.js page by page as they scroll
// into view, paints one highlight region per marked passage from the page's
// text items (never from the text-layer DOM), places the pre-rendered cards
// in the rail beside their passages, and draws a band across the gutter
// from each passage to its card. Geometry comes from manuscript-place.js;
// this file is the DOM and pdf.js glue.
//
// Runs under the page CSP: pdf.js and its worker are same-origin files
// named in the data attributes, and the PDF is fetched from the same origin.
(() => {
  const root = document.querySelector('.manuscript[data-pdf]');
  const place = window.laxManuscript;
  if (!root || !place) return;
  const pagesEl = document.getElementById('manuscript-pages');
  const railEl = document.getElementById('manuscript-rail');
  const linksEl = document.getElementById('manuscript-links');
  const bodyEl = pagesEl && pagesEl.parentElement;
  const statusEl = document.getElementById('manuscript-status');
  const dataEl = document.getElementById('manuscript-data');
  if (!pagesEl || !railEl || !dataEl) return;

  const data = JSON.parse(dataEl.textContent || '{}');
  const marks = Array.isArray(data.marks) ? data.marks : [];
  const RENDER_MARGIN = '900px';
  const CARD_GAP = 8;
  const SHADOW_MARGIN = 18; // px beyond the passage's leftmost and rightmost extent
  const SVG = 'http://www.w3.org/2000/svg';

  const pageEls = [...pagesEl.querySelectorAll('.manuscript-page')];
  const cards = marks.map((mark) => {
    const el = document.getElementById(`m${mark.n}`);
    return { mark, el, hits: [], rects: [], shadows: [], shadowX: null, band: null, want: 0, resolved: null, link: null, pinned: false };
  }).filter((card) => card.el);

  const setStatus = (text, failed = false) => {
    if (!statusEl) return;
    statusEl.textContent = text;
    statusEl.classList.toggle('manuscript-status-failed', failed);
  };

  // ---- pdf.js ----

  let pdfjs;
  let doc;
  const pageState = []; // per page: { page, viewport, text, analysed, rendered, task, el, hl }
  let scale = 1;

  async function loadDocument() {
    pdfjs = await import(root.dataset.pdfjs);
    pdfjs.GlobalWorkerOptions.workerSrc = new URL(root.dataset.pdfjsWorker, location.href).href;
    const url = new URL(root.dataset.pdf, location.href).href;
    doc = await pdfjs.getDocument({ url, isEvalSupported: false }).promise;
    for (let p = 1; p <= doc.numPages; p++) {
      const el = pageEls[p - 1];
      if (!el) break;
      const hl = document.createElementNS(SVG, 'svg');
      hl.setAttribute('class', 'manuscript-hl-layer');
      const shadows = document.createElementNS(SVG, 'g');
      const shapes = document.createElementNS(SVG, 'g');
      hl.append(shadows, shapes);
      el.append(hl);
      pageState.push({ number: p, page: null, viewport: null, text: null, analysed: null, rendered: false, task: null, el, hl, shadows, shapes });
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
    for (const child of [...state.el.children]) if (child !== state.hl) child.remove();
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

  // Per passage: one flat region per column run on each page it touches,
  // and behind them a lighter shadow — a fixed margin beyond the passage's
  // leftmost and rightmost extent over all its pages, so its edges are
  // straight from page to page, running to the foot of a page it leaves
  // and from the head of a page it continues on. The gutter band starts
  // at its right edge.
  async function paintHighlights() {
    for (const state of pageState) { state.shadows.replaceChildren(); state.shapes.replaceChildren(); }
    for (const card of cards) {
      card.hits = [];
      card.rects = [];
      card.shadows = [];
      card.shadowX = null;
      if (!card.resolved) continue;
      const kind = `kind-${card.mark.kind}`;
      const segments = card.resolved.segments;
      const spans = [];
      for (const seg of segments) {
        const state = pageState[seg.page - 1];
        const viewport = await viewportOf(state);
        state.hl.setAttribute('viewBox', `0 0 ${viewport.width} ${viewport.height}`);
        let top = Infinity;
        let bottom = -Infinity;
        for (const shape of place.segmentShapes(state.analysed, seg)) {
          const points = shape.points.map(([x, y]) => viewport.convertToViewportPoint(x, y));
          const [ax, ay] = viewport.convertToViewportPoint(shape.x0, shape.top);
          const [bx, by] = viewport.convertToViewportPoint(shape.x1, shape.bot);
          const rect = { page: seg.page, left: Math.min(ax, bx), top: Math.min(ay, by), width: Math.abs(bx - ax), height: Math.abs(by - ay) };
          const path = svgNode('path', { class: `manuscript-hl ${kind}`, d: `M${points.map(([x, y]) => `${x.toFixed(2)},${y.toFixed(2)}`).join('L')}Z` });
          state.shapes.append(path);
          card.hits.push(path);
          card.rects.push(rect);
          top = Math.min(top, rect.top);
          bottom = Math.max(bottom, rect.top + rect.height);
        }
        spans.push({ state, viewport, page: seg.page, top, bottom });
      }
      if (!card.rects.length) continue;
      const width = spans[0].viewport.width;
      const x0 = Math.max(0, Math.min(...card.rects.map((r) => r.left)) - SHADOW_MARGIN);
      const x1 = Math.min(width, Math.max(...card.rects.map((r) => r.left + r.width)) + SHADOW_MARGIN);
      card.shadowX = { x0, x1 };
      spans.forEach((span, i) => {
        if (span.top >= span.bottom) return;
        const top = i > 0 ? 0 : span.top;
        const bottom = i < spans.length - 1 ? span.viewport.height : span.bottom;
        const shadow = svgNode('rect', { class: `manuscript-hl-shadow ${kind}`, x: x0.toFixed(2), y: top.toFixed(2), width: (x1 - x0).toFixed(2), height: (bottom - top).toFixed(2) });
        span.state.shadows.append(shadow);
        card.hits.push(shadow);
        card.shadows.push({ page: span.page, top, bottom });
      });
    }
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

  // The rail is always beside the pages (the body scrolls sideways where
  // the screen is narrower than the two together), so cards sit at their
  // passages' y from the first layout on.
  function stack() {
    railEl.classList.add('manuscript-rail-live');
    const tops = place.stackCards(cards.map((card) => ({ want: card.want, height: card.el.offsetHeight })), CARD_GAP);
    let bottom = 0;
    cards.forEach((card, index) => {
      card.el.style.top = `${tops[index]}px`;
      bottom = Math.max(bottom, tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(pagesEl.offsetHeight, bottom + 24)}px`;
    drawLinks();
  }

  // The band from a passage to its card, split-diff style: the passage's
  // shadow at its right edge (the gap between pages included), the whole
  // card at the rail's left edge, cubic curves between. Coordinates are
  // the body's.
  function drawLinks() {
    if (!linksEl || !bodyEl) return;
    const width = bodyEl.clientWidth;
    const height = bodyEl.clientHeight;
    linksEl.setAttribute('viewBox', `0 0 ${width} ${height}`);
    linksEl.classList.add('manuscript-links-live');
    // The band starts a pixel inside the shadow's right edge so the two
    // meet without a seam, and ends under the card's border.
    const xr = railEl.offsetLeft + 2;
    for (const card of cards) {
      if (!card.shadows.length) { if (card.link) { card.link.remove(); card.link = null; } card.band = null; continue; }
      const xl = pagesEl.offsetLeft + pageState[0].el.clientLeft + card.shadowX.x1 - 1;
      const xm = (xl + xr) / 2;
      const first = card.shadows[0];
      const last = card.shadows[card.shadows.length - 1];
      const top = pagesEl.offsetTop + pageState[first.page - 1].el.offsetTop + first.top;
      const bottom = pagesEl.offsetTop + pageState[last.page - 1].el.offsetTop + last.bottom;
      const ct = railEl.offsetTop + card.el.offsetTop;
      const cb = ct + card.el.offsetHeight;
      const d = `M${xl},${top.toFixed(1)} C${xm},${top.toFixed(1)} ${xm},${ct} ${xr},${ct} L${xr},${cb} C${xm},${cb} ${xm},${bottom.toFixed(1)} ${xl},${bottom.toFixed(1)} Z`;
      if (!card.link) {
        card.link = svgNode('path', { class: `manuscript-link kind-${card.mark.kind}` });
        linksEl.append(card.link);
      }
      card.link.setAttribute('d', d);
      // The ribbon's geometry, for hit-testing: the shadow's column over
      // the pages (gaps included) and the band across the gutter.
      card.band = { xs0: xl + 1 - (card.shadowX.x1 - card.shadowX.x0), xl, xm, xr, top, bottom, ct, cb };
    }
  }

  // Whether (x, y), in the body's coordinates, lies on a card's ribbon:
  // in the shadow's column between the passage's first and last line
  // (the gaps between pages included), or inside the gutter band, whose
  // edges are the cubic curves drawLinks draws.
  function ribbonContains(band, x, y) {
    if (x >= band.xs0 && x <= band.xl) return y >= band.top && y <= band.bottom;
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

  // The card in front: its band drawn over the others.
  function raise(card) {
    if (card.link && linksEl && linksEl.lastElementChild !== card.link) linksEl.append(card.link);
  }

  function setExpanded(card, expanded) {
    card.el.classList.toggle('manuscript-card-expanded', expanded);
    const body = card.el.querySelector('.manuscript-card-body');
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (body) body.hidden = !expanded;
    if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
    for (const hit of card.hits) hit.classList.toggle('manuscript-hl-active', expanded);
    stack();
    if (card.link) card.link.classList.toggle('manuscript-link-active', expanded);
    if (expanded) raise(card);
  }

  // A card opens while hovered — from the rail or from its passage — and
  // stays open once pinned by a click.
  function setHover(card, hovering) {
    for (const hit of card.hits) hit.classList.toggle('manuscript-hl-hover', hovering);
    if (card.link) card.link.classList.toggle('manuscript-link-hover', hovering);
    if (hovering) raise(card);
    if (!card.pinned && isExpanded(card) !== hovering) setExpanded(card, hovering);
  }

  function setPinned(card, pinned) {
    card.pinned = pinned;
    card.el.classList.toggle('manuscript-card-pinned', pinned);
    if (isExpanded(card) !== pinned) setExpanded(card, pinned);
  }

  function isExpanded(card) {
    return card.el.classList.contains('manuscript-card-expanded');
  }

  function scrollToPassage(card) {
    const first = card.hits[0];
    const target = first || pageState[card.mark.begin.page - 1]?.el;
    if (!target) return;
    const box = target.getBoundingClientRect();
    const header = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--header-height')) || 0;
    window.scrollTo({ top: window.scrollY + box.top - header * 16 - 120, behavior: 'smooth' });
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
        setPinned(card, !card.pinned);
        scrollToPassage(card);
      });
      card.el.addEventListener('mouseenter', () => setHover(card, true));
      card.el.addEventListener('mouseleave', () => setHover(card, false));
    }
    // Highlights take no pointer events so the text under them stays
    // selectable; clicks and hovers are hit-tested here, the innermost
    // passage winning.
    const cardAt = (event) => {
      const pageEl = event.target.closest('.manuscript-page');
      if (!pageEl || event.target.closest('a')) return null;
      const pageNumber = Number(pageEl.dataset.page);
      const box = pageEl.getBoundingClientRect();
      const x = event.clientX - box.left;
      const y = event.clientY - box.top;
      let best = null;
      let bestArea = Infinity;
      for (const card of cards) {
        for (const rect of card.rects) {
          if (rect.page !== pageNumber) continue;
          if (x < rect.left || x > rect.left + rect.width || y < rect.top || y > rect.top + rect.height) continue;
          const area = card.rects.reduce((sum, r) => sum + r.width * r.height, 0);
          if (area < bestArea) { best = card; bestArea = area; }
        }
      }
      if (best) return best;
      // off the text: the shadow, the shortest passage winning
      let bestSpan = Infinity;
      for (const card of cards) {
        for (const shadow of card.shadows) {
          if (shadow.page !== pageNumber || y < shadow.top || y > shadow.bottom) continue;
          if (x < card.shadowX.x0 || x > card.shadowX.x1) continue;
          const span = card.shadows.reduce((sum, s) => sum + s.bottom - s.top, 0);
          if (span < bestSpan) { best = card; bestSpan = span; }
        }
      }
      return best;
    };
    // Off the pages — the gap between two pages, or the gutter — the
    // ribbon is the target too, the one drawn in front winning.
    const cardAtRibbon = (event) => {
      if (!bodyEl || !linksEl || event.target.closest('.manuscript-page, .manuscript-rail, a')) return null;
      const box = bodyEl.getBoundingClientRect();
      const x = event.clientX - box.left + bodyEl.scrollLeft;
      const y = event.clientY - box.top + bodyEl.scrollTop;
      let best = null;
      let bestOrder = -1;
      for (const card of cards) {
        if (!card.band || !card.link || !ribbonContains(card.band, x, y)) continue;
        const order = Array.prototype.indexOf.call(linksEl.children, card.link);
        if (order > bestOrder) { best = card; bestOrder = order; }
      }
      return best;
    };
    const hoverSurface = bodyEl || pagesEl;
    let hovered = null;
    hoverSurface.addEventListener('mousemove', (event) => {
      if (event.target.closest('.manuscript-rail')) return;
      const card = cardAt(event) || cardAtRibbon(event);
      if (card === hovered) return;
      if (hovered) { setHover(hovered, false); hovered.el.classList.remove('manuscript-card-hover'); }
      hovered = card;
      if (hovered) { setHover(hovered, true); hovered.el.classList.add('manuscript-card-hover'); }
    });
    hoverSurface.addEventListener('mouseleave', () => {
      if (hovered) { setHover(hovered, false); hovered.el.classList.remove('manuscript-card-hover'); }
      hovered = null;
    });
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

  main().catch((error) => {
    console.error('paper viewer failed', error);
    setStatus(`The paper could not be shown here (${error && error.message ? error.message : error}). Download the PDF instead.`, true);
    root.classList.add('manuscript-failed');
  });
})();
