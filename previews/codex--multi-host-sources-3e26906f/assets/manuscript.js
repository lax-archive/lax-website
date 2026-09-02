// The paper viewer: renders the PDF with pdf.js page by page as they scroll
// into view, paints one highlight per marked passage from the page's text
// items (never from the text-layer DOM), and places the pre-rendered cards
// in the rail beside their passages. Geometry comes from
// manuscript-place.js; this file is the DOM and pdf.js glue.
//
// Runs under the page CSP: pdf.js and its worker are same-origin files
// named in the data attributes, and the PDF is fetched from the same origin.
(() => {
  const root = document.querySelector('.manuscript[data-pdf]');
  const place = window.laxManuscript;
  if (!root || !place) return;
  const pagesEl = document.getElementById('manuscript-pages');
  const railEl = document.getElementById('manuscript-rail');
  const statusEl = document.getElementById('manuscript-status');
  const dataEl = document.getElementById('manuscript-data');
  if (!pagesEl || !railEl || !dataEl) return;

  const data = JSON.parse(dataEl.textContent || '{}');
  const marks = Array.isArray(data.marks) ? data.marks : [];
  const RENDER_MARGIN = '900px';
  const CARD_GAP = 8;
  const sideRail = window.matchMedia('(min-width: 1101px)');

  const pageEls = [...pagesEl.querySelectorAll('.manuscript-page')];
  const cards = marks.map((mark) => {
    const el = document.getElementById(`m${mark.n}`);
    return { mark, el, hits: [], rects: [], want: 0, resolved: null };
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
      const hl = document.createElement('div');
      hl.className = 'manuscript-hl-layer';
      el.append(hl);
      pageState.push({ number: p, page: null, viewport: null, text: null, analysed: null, rendered: false, task: null, el, hl });
    }
  }

  async function pdfPage(state) {
    if (!state.page) state.page = await doc.getPage(state.number);
    return state.page;
  }

  async function pageText(state) {
    if (!state.text) {
      const page = await pdfPage(state);
      state.text = await page.getTextContent();
      state.analysed = place.analyzePage(place.textItems(state.text));
    }
    return state.text;
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

  async function paintHighlights() {
    for (const state of pageState) state.hl.replaceChildren();
    for (const card of cards) {
      card.hits = [];
      card.rects = [];
      if (!card.resolved) continue;
      for (const seg of card.resolved.segments) {
        const state = pageState[seg.page - 1];
        const viewport = await viewportOf(state);
        for (const r of place.segmentRects(state.analysed, seg)) {
          const [ax, ay] = viewport.convertToViewportPoint(r.x0, r.top);
          const [bx, by] = viewport.convertToViewportPoint(r.x1, r.bot);
          const rect = { page: seg.page, left: Math.min(ax, bx), top: Math.min(ay, by), width: Math.abs(bx - ax), height: Math.abs(by - ay) };
          const div = document.createElement('div');
          div.className = `manuscript-hl kind-${card.mark.kind}`;
          div.style.left = `${rect.left}px`;
          div.style.top = `${rect.top}px`;
          div.style.width = `${rect.width}px`;
          div.style.height = `${rect.height}px`;
          div.style.zIndex = String(10 + card.mark.n);
          state.hl.append(div);
          card.hits.push(div);
          card.rects.push(rect);
        }
      }
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

  function stack() {
    if (!sideRail.matches) {
      railEl.classList.remove('manuscript-rail-live');
      railEl.style.height = '';
      for (const card of cards) card.el.style.top = '';
      return;
    }
    railEl.classList.add('manuscript-rail-live');
    const tops = place.stackCards(cards.map((card) => ({ want: card.want, height: card.el.offsetHeight })), CARD_GAP);
    let bottom = 0;
    cards.forEach((card, index) => {
      card.el.style.top = `${tops[index]}px`;
      bottom = Math.max(bottom, tops[index] + card.el.offsetHeight);
    });
    railEl.style.height = `${Math.max(pagesEl.offsetHeight, bottom + 24)}px`;
  }

  function setExpanded(card, expanded) {
    card.el.classList.toggle('manuscript-card-expanded', expanded);
    const body = card.el.querySelector('.manuscript-card-body');
    const toggle = card.el.querySelector('.manuscript-card-toggle');
    if (body) body.hidden = !expanded;
    if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
    for (const hit of card.hits) hit.classList.toggle('manuscript-hl-active', expanded);
    stack();
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
        setExpanded(card, !isExpanded(card));
      });
      card.el.addEventListener('click', (event) => {
        if (event.target.closest('a, button')) return;
        setExpanded(card, !isExpanded(card));
        scrollToPassage(card);
      });
    }
    // Highlights take no pointer events so the text under them stays
    // selectable; clicks are hit-tested here, the innermost passage winning.
    pagesEl.addEventListener('click', (event) => {
      const pageEl = event.target.closest('.manuscript-page');
      if (!pageEl || event.target.closest('a')) return;
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
      if (!best) return;
      const expanded = !isExpanded(best);
      setExpanded(best, expanded);
      flash(best);
      if (!sideRail.matches && expanded) best.el.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    });
  }

  function openFromHash() {
    const match = /^#m(\d+)$/.exec(location.hash);
    if (!match) return;
    const card = cards.find((c) => c.mark.n === Number(match[1]));
    if (!card) return;
    setExpanded(card, true);
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
    sideRail.addEventListener('change', () => stack());
    if ('ResizeObserver' in window) new ResizeObserver(onResize).observe(pagesEl);
    document.fonts?.ready.then(() => stack());
  }

  main().catch((error) => {
    console.error('paper viewer failed', error);
    setStatus(`The paper could not be shown here (${error && error.message ? error.message : error}). Download the PDF instead.`, true);
    root.classList.add('manuscript-failed');
  });
})();
