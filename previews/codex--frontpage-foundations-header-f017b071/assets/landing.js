// The landing page: the "Browse submissions" button scrolls to the library
// and keeps a shareable ?view= URL in sync; each example joins its
// highlighted passages to their cards the way the paper page does — hover
// opens the card, a click pins it open; the tabs above the examples switch
// between them; the proof network is centred in its box.
(() => {
  // The front page opens with its two orientation links directly below the
  // archive name. Once the reader moves into the page, restore the compact
  // side-by-side masthead used everywhere else.
  function setupLandingHeader() {
    const header = document.querySelector('.site-header.landing-header');
    if (!header) return;
    let frame;

    function update() {
      frame = undefined;
      header.classList.toggle('landing-header-scrolled', window.scrollY > 1);
    }

    function queueUpdate() {
      if (frame !== undefined) return;
      frame = requestAnimationFrame(update);
    }

    window.addEventListener('scroll', queueUpdate, { passive: true });
    update();
  }

  function setupSetupTabs() {
    for (const root of document.querySelectorAll('[data-setup-tabs]')) {
      const tabs = [...root.querySelectorAll('[role="tab"]')];
      const panels = tabs.map((tab) => document.getElementById(tab.getAttribute('aria-controls')));

      function select(index, focus) {
        tabs.forEach((tab, tabIndex) => {
          const selected = tabIndex === index;
          tab.setAttribute('aria-selected', String(selected));
          tab.tabIndex = selected ? 0 : -1;
          if (panels[tabIndex]) panels[tabIndex].hidden = !selected;
        });
        if (focus) tabs[index].focus();
      }

      tabs.forEach((tab, index) => {
        tab.addEventListener('click', () => select(index, false));
        tab.addEventListener('keydown', (event) => {
          let next;
          if (event.key === 'ArrowRight') next = (index + 1) % tabs.length;
          else if (event.key === 'ArrowLeft') next = (index - 1 + tabs.length) % tabs.length;
          else if (event.key === 'Home') next = 0;
          else if (event.key === 'End') next = tabs.length - 1;
          else return;
          event.preventDefault();
          select(next, true);
        });
      });
    }
  }

  function setupLandingActions() {
    const buttons = [...document.querySelectorAll('[data-landing-action]')];
    if (!buttons.length) return;
    const viewIds = new Set(buttons.map((button) => button.dataset.landingAction));

    function urlView() {
      const id = new URLSearchParams(window.location.search).get('view');
      return viewIds.has(id) ? id : undefined;
    }

    function updateUrl(id) {
      const url = new URL(window.location.href);
      const current = url.searchParams.get('view');
      if (id) url.searchParams.set('view', id);
      else url.searchParams.delete('view');
      if (current === (id ?? null)) return;
      window.history.pushState(null, '', `${url.pathname}${url.search}${url.hash}`);
    }

    function scrollToView(id) {
      const target = document.getElementById(`landing-panel-${id}`);
      if (!target) return;
      const behavior = window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth';
      requestAnimationFrame(() => requestAnimationFrame(() => {
        target.scrollIntoView({ behavior, block: 'start' });
      }));
    }

    function selectView(id, updateHistory) {
      if (updateHistory) updateUrl(id);
      scrollToView(id);
    }

    for (const button of buttons) {
      button.addEventListener('click', () => {
        selectView(button.dataset.landingAction, true);
      });
    }

    window.addEventListener('popstate', () => {
      const id = urlView();
      if (id) selectView(id, false);
    });

    const initialView = urlView();
    if (initialView) selectView(initialView, false);
  }

  const CARD_GAP = 8;

  // A box of cards: the paper excerpt (passages in a text column, their
  // cards in a rail beside it, bands between them) or the inference (cards
  // alone). Hover opens a card, a click pins it; a card that opened with
  // the page stays open only until the reader's first hover anywhere in
  // the box, then every card follows the usual rule. Under the cards a
  // hint says what to do, until the first hover or tap. On a phone there
  // is no rail: each card sits in the text under its passage.
  function setupCardBox(box) {
    const grid = box.querySelector('.landing-paper-grid');
    const doc = box.querySelector('.landing-paper-doc');
    const rail = box.querySelector('.landing-paper-rail');
    const links = box.querySelector('.landing-paper-links');
    const hint = box.querySelector('.landing-paper-hint');
    const canHover = window.matchMedia('(hover: hover)');
    const narrow = window.matchMedia('(max-width: 640px)');
    const pairs = [];

    // Each card at its passage's height, pushed down where it would overlap
    // the card above. A card takes the room it has closed — except one
    // that opened with the page or that the reader pinned — so a card
    // opening under the pointer lies over the cards below it instead of
    // shoving them down, and the box is as tall as the cards at rest. On a
    // phone each card goes into the text under its passage (and back to
    // the rail when the screen widens).
    function placeCards() {
      if (!doc || !rail) return;
      const placed = pairs.filter((pair) => pair.passage);
      if (narrow.matches) {
        rail.classList.remove('landing-paper-rail-live');
        rail.classList.add('landing-paper-rail-inline');
        rail.style.minHeight = '';
        // The hint lies over the text's first lines, in no room of
        // its own, so nothing shifts when it goes.
        if (hint && doc.firstElementChild !== hint) { hint.style.top = ''; doc.prepend(hint); }
        for (const { passage, card } of placed) {
          card.style.top = '';
          card.classList.add('landing-card-inline');
          if (passage.nextElementSibling !== card) passage.after(card);
        }
        return;
      }
      if (rail.classList.contains('landing-paper-rail-inline')) {
        rail.classList.remove('landing-paper-rail-inline');
        for (const { card } of pairs) {
          card.classList.remove('landing-card-inline');
          rail.append(card);
        }
        if (hint) rail.append(hint);
      }
      rail.classList.add('landing-paper-rail-live');
      const docTop = doc.getBoundingClientRect().top;
      let bottom = 0;
      let first = Infinity;
      for (const pair of placed) {
        const { passage, card } = pair;
        const wanted = passage.getBoundingClientRect().top - docTop;
        const y = Math.max(wanted, bottom);
        card.style.top = `${y}px`;
        first = Math.min(first, y);
        bottom = y + (pair.opening || pair.pinned ? card.offsetHeight : closedHeight(card)) + CARD_GAP;
      }
      // The hint in the room above the first card — the rail's top, where
      // the paper's prose runs before its first passage — or, where there
      // is none, under the last card.
      if (hint) {
        if (first >= hint.offsetHeight + CARD_GAP) hint.style.top = '0px';
        else {
          hint.style.top = `${bottom}px`;
          bottom += hint.offsetHeight + CARD_GAP;
        }
      }
      rail.style.minHeight = `${Math.max(0, bottom - CARD_GAP)}px`;
    }

    // The first hover or tap in any example takes the hints away, in
    // every example: the reader knows.
    function touched() {
      (box.closest('[data-carousel]') || box).classList.add('landing-paper-touched');
    }

    // A card's height with its body closed.
    function closedHeight(card) {
      const body = card.querySelector('.manuscript-card-body');
      if (!body || body.hidden) return card.offsetHeight;
      return card.offsetHeight - body.offsetHeight - parseFloat(getComputedStyle(body).marginTop || '0');
    }

    // The band from a passage to its card, the paper page's split-diff
    // shape: the passage's right edge, the card's left edge, cubic curves
    // across the gutter. Coordinates are the grid's. Nothing in one column.
    function drawLinks() {
      if (!grid || !links) return;
      if (narrow.matches) {
        links.classList.remove('manuscript-links-live');
        return;
      }
      const box = grid.getBoundingClientRect();
      links.setAttribute('viewBox', `0 0 ${grid.clientWidth} ${grid.clientHeight}`);
      links.classList.add('manuscript-links-live');
      for (const pair of pairs) {
        if (!pair.passage) continue;
        const p = pair.passage.getBoundingClientRect();
        const c = pair.card.getBoundingClientRect();
        const xl = p.right - box.left - 1;
        const xr = c.left - box.left + 1;
        const xm = (xl + xr) / 2;
        const top = p.top - box.top;
        const bottom = p.bottom - box.top;
        const ct = c.top - box.top;
        const cb = c.bottom - box.top;
        if (!pair.link) {
          pair.link = document.createElementNS('http://www.w3.org/2000/svg', 'path');
          pair.link.setAttribute('class', `manuscript-link kind-${pair.passage.dataset.kind || 'concept'}`);
          links.append(pair.link);
        }
        pair.link.setAttribute('d', `M${xl.toFixed(1)},${top.toFixed(1)} C${xm.toFixed(1)},${top.toFixed(1)} ${xm.toFixed(1)},${ct.toFixed(1)} ${xr.toFixed(1)},${ct.toFixed(1)} L${xr.toFixed(1)},${cb.toFixed(1)} C${xm.toFixed(1)},${cb.toFixed(1)} ${xm.toFixed(1)},${bottom.toFixed(1)} ${xl.toFixed(1)},${bottom.toFixed(1)} Z`);
      }
    }

    function layout() {
      placeCards();
      drawLinks();
    }

    function clearOpening(except) {
      for (const other of pairs) {
        if (other === except || !other.opening) continue;
        other.opening = false;
        other.close();
      }
    }

    for (const card of box.querySelectorAll('.manuscript-card')) {
      const passage = card.id ? box.querySelector(`[data-excerpt-card="${CSS.escape(card.id)}"]`) : null;
      const pair = { passage, card, link: null, opening: card.classList.contains('manuscript-card-expanded'), pinned: false, close: () => undefined };
      pairs.push(pair);
      const body = card.querySelector('.manuscript-card-body');
      const toggle = card.querySelector('.manuscript-card-toggle');
      pair.close = () => { if (!pair.pinned) setExpanded(false); };

      function setExpanded(expanded) {
        card.classList.toggle('manuscript-card-expanded', expanded);
        if (body) body.hidden = !expanded;
        if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
        if (passage) passage.classList.toggle('manuscript-hl-active', expanded);
        if (pair.link) pair.link.classList.toggle('manuscript-link-active', expanded);
        layout();
      }

      function setHover(hovering) {
        if (hovering) touched();
        if (hovering) clearOpening(pair);
        else pair.opening = false;
        if (passage) passage.classList.toggle('manuscript-hl-hover', hovering);
        card.classList.toggle('manuscript-card-hover', hovering);
        if (pair.link) pair.link.classList.toggle('manuscript-link-hover', hovering);
        if (!pair.pinned) setExpanded(hovering);
      }

      function setPinned(next) {
        touched();
        pair.opening = false;
        clearOpening(pair);
        pair.pinned = next;
        card.classList.toggle('manuscript-card-pinned', next);
        if (passage) passage.setAttribute('aria-pressed', String(next));
        setExpanded(next);
      }

      for (const el of [passage, card]) {
        if (!el) continue;
        el.addEventListener('mouseenter', () => { if (canHover.matches) setHover(true); });
        el.addEventListener('mouseleave', () => { if (canHover.matches) setHover(false); });
      }
      if (passage) {
        passage.addEventListener('click', () => setPinned(!pair.pinned));
        passage.addEventListener('keydown', (event) => {
          if (event.key !== 'Enter' && event.key !== ' ') return;
          event.preventDefault();
          setPinned(!pair.pinned);
        });
      }
      card.addEventListener('click', (event) => {
        // Links in the card lead away; the body is for reading and selecting.
        if (event.target.closest('a') || (body && body.contains(event.target))) return;
        setPinned(!pair.pinned);
      });
    }

    // Anything that moves a passage or resizes a card — the window, the
    // sidebar, fonts arriving, a card opening — lays the rail out again.
    if (typeof ResizeObserver === 'function') {
      const observer = new ResizeObserver(() => layout());
      for (const el of [grid, doc, rail, ...pairs.map((pair) => pair.card)]) if (el) observer.observe(el);
    }
    window.addEventListener('resize', layout);
    narrow.addEventListener('change', layout);
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(layout);
    layout();
  }

  function setupCardBoxes() {
    for (const box of document.querySelectorAll('[data-card-box]')) setupCardBox(box);
  }

  // The examples: one dot per example, a large arrow either side of the
  // box to step through them, and the left and right arrow keys anywhere
  // on the page outside a field or a scrolling figure. Nothing moves on
  // its own. The slides stay in the page: an inactive one is out of flow,
  // invisible and inert, and the box eases its height from one slide to
  // the next.
  function setupCarousel(root) {
    const tabs = [...root.querySelectorAll('[role="tab"]')];
    if (tabs.length < 2) return;
    const slides = tabs.map((tab) => document.getElementById(tab.getAttribute('aria-controls')));
    const stage = root.querySelector('.landing-carousel-slides');
    const reduceMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
    let current = Math.max(0, tabs.findIndex((tab) => tab.getAttribute('aria-selected') === 'true'));

    function select(index, focus) {
      const next = (index + tabs.length) % tabs.length;
      const from = stage ? stage.offsetHeight : 0;
      current = next;
      tabs.forEach((tab, i) => {
        const selected = i === current;
        tab.setAttribute('aria-selected', String(selected));
        tab.tabIndex = selected ? 0 : -1;
        const slide = slides[i];
        if (!slide) return;
        slide.classList.toggle('landing-carousel-slide-off', !selected);
        if (selected) {
          slide.removeAttribute('aria-hidden');
          slide.removeAttribute('inert');
        } else {
          slide.setAttribute('aria-hidden', 'true');
          slide.setAttribute('inert', '');
        }
      });
      if (stage && from && !reduceMotion.matches) {
        const to = stage.offsetHeight;
        if (to !== from) {
          stage.style.height = `${from}px`;
          void stage.offsetHeight;
          stage.style.height = `${to}px`;
          const done = (event) => {
            if (event.target !== stage) return;
            stage.style.height = '';
            stage.removeEventListener('transitionend', done);
          };
          stage.addEventListener('transitionend', done);
        }
      }
      if (focus) tabs[current].focus();
    }

    tabs.forEach((tab, index) => {
      tab.addEventListener('click', () => { if (index !== current) select(index, false); });
      tab.addEventListener('keydown', (event) => {
        if (event.key === 'ArrowRight' || event.key === 'ArrowDown') select(index + 1, true);
        else if (event.key === 'ArrowLeft' || event.key === 'ArrowUp') select(index - 1, true);
        else if (event.key === 'Home') select(0, true);
        else if (event.key === 'End') select(tabs.length - 1, true);
        else return;
        event.preventDefault();
      });
    });
    for (const arrow of root.querySelectorAll('[data-carousel-step]')) {
      arrow.addEventListener('click', () => select(current + Number(arrow.dataset.carouselStep || 1), false));
    }
    document.addEventListener('keydown', (event) => {
      if (event.key !== 'ArrowLeft' && event.key !== 'ArrowRight') return;
      if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
      const target = event.target;
      if (target && target !== document.body && !root.contains(target)) return;
      select(current + (event.key === 'ArrowRight' ? 1 : -1), false);
      event.preventDefault();
    });
    select(current, false);
  }

  function setupCarousels() {
    for (const root of document.querySelectorAll('[data-carousel]')) setupCarousel(root);
  }

  // The proof network is wider than its box, and may be taller. On a
  // desktop it is scaled down to the box's height, so the whole of it is
  // in view top to bottom and only scrolls sideways, centred (the large
  // window shows it at full size); on a phone it keeps its size, centred,
  // as the box is as tall as the graph there. Again whenever dag.js draws
  // it (on load, after a resize, on opening or closing the large window).
  function setupNetwork() {
    const container = document.getElementById('proof-network');
    if (!container) return;
    const figure = container.closest('.graph-figure');
    const narrow = window.matchMedia('(max-width: 640px)');
    function fit() {
      const svg = container.querySelector('svg');
      if (!svg) return;
      const natural = Number(svg.getAttribute('height')) || svg.getBoundingClientRect().height;
      const cap = parseFloat(getComputedStyle(container).maxHeight);
      const fitted = !narrow.matches && !(figure && figure.classList.contains('graph-expanded')) && Number.isFinite(cap) && cap < natural;
      if (fitted) {
        svg.style.height = `${cap}px`;
        svg.style.width = 'auto';
        container.style.height = `${cap}px`;
      } else {
        svg.style.height = '';
        svg.style.width = '';
        container.style.height = `${natural}px`;
      }
      container.scrollLeft = Math.max(0, (container.scrollWidth - container.clientWidth) / 2);
    }
    if (typeof MutationObserver === 'function') new MutationObserver(fit).observe(container, { childList: true });
    narrow.addEventListener('change', fit);
    fit();
  }

  function setupLanding() {
    setupLandingHeader();
    setupSetupTabs();
    setupLandingActions();
    setupCardBoxes();
    setupCarousels();
    setupNetwork();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', setupLanding);
  else setupLanding();
})();
