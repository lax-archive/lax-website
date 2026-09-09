// The landing page: the "Browse submissions" button scrolls to the library
// and keeps a shareable ?view= URL in sync; the paper excerpt joins each
// highlighted passage to its concept card the way the paper page does —
// hover opens the card, a click pins it open.
(() => {
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

  function setupPaperExcerpt() {
    const excerpt = document.querySelector('[data-paper-excerpt]');
    if (!excerpt) return;
    const doc = excerpt.querySelector('.landing-paper-doc');
    const rail = excerpt.querySelector('.landing-paper-rail');
    const canHover = window.matchMedia('(hover: hover)');
    const narrow = window.matchMedia('(max-width: 640px)');
    const pairs = [];

    // Each card at its passage's height, pushed down where it would overlap
    // the card above; in one column the cards stay in flow under the text.
    function placeCards() {
      if (!doc || !rail) return;
      if (narrow.matches) {
        rail.classList.remove('landing-paper-rail-live');
        for (const { card } of pairs) card.style.top = '';
        rail.style.minHeight = '';
        return;
      }
      rail.classList.add('landing-paper-rail-live');
      const docTop = doc.getBoundingClientRect().top;
      let bottom = 0;
      for (const { passage, card } of pairs) {
        const y = Math.max(passage.getBoundingClientRect().top - docTop, bottom);
        card.style.top = `${y}px`;
        bottom = y + card.offsetHeight + CARD_GAP;
      }
      rail.style.minHeight = `${Math.max(0, bottom - CARD_GAP)}px`;
    }

    for (const passage of excerpt.querySelectorAll('[data-excerpt-card]')) {
      const card = document.getElementById(passage.dataset.excerptCard);
      if (!card) continue;
      pairs.push({ passage, card });
      const body = card.querySelector('.manuscript-card-body');
      const toggle = card.querySelector('.manuscript-card-toggle');
      let pinned = card.classList.contains('manuscript-card-pinned');

      function setExpanded(expanded) {
        card.classList.toggle('manuscript-card-expanded', expanded);
        if (body) body.hidden = !expanded;
        if (toggle) toggle.setAttribute('aria-expanded', String(expanded));
        passage.classList.toggle('manuscript-hl-active', expanded);
        placeCards();
      }

      function setHover(hovering) {
        passage.classList.toggle('manuscript-hl-hover', hovering);
        card.classList.toggle('manuscript-card-hover', hovering);
        if (!pinned) setExpanded(hovering);
      }

      function setPinned(next) {
        pinned = next;
        card.classList.toggle('manuscript-card-pinned', pinned);
        passage.setAttribute('aria-pressed', String(pinned));
        setExpanded(pinned);
      }

      for (const el of [passage, card]) {
        el.addEventListener('mouseenter', () => { if (canHover.matches) setHover(true); });
        el.addEventListener('mouseleave', () => { if (canHover.matches) setHover(false); });
      }
      passage.addEventListener('click', () => setPinned(!pinned));
      passage.addEventListener('keydown', (event) => {
        if (event.key !== 'Enter' && event.key !== ' ') return;
        event.preventDefault();
        setPinned(!pinned);
      });
      card.addEventListener('click', (event) => {
        // Links in the card lead away; the body is for reading and selecting.
        if (event.target.closest('a') || (body && body.contains(event.target))) return;
        setPinned(!pinned);
      });
    }

    window.addEventListener('resize', placeCards);
    narrow.addEventListener('change', placeCards);
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(placeCards);
    placeCards();
  }

  function setupLanding() {
    setupLandingActions();
    setupPaperExcerpt();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', setupLanding);
  else setupLanding();
})();
