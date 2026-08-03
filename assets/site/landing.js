// Landing-page action cards disclose one focused panel at a time. The
// content is already in the static HTML; this manages visibility, accessible
// expanded state, and shareable ?view= URLs.
(() => {
  function setupLandingActions() {
    const buttons = [...document.querySelectorAll('[data-landing-action]')];
    if (!buttons.length) return;
    const views = [...document.querySelectorAll('[data-landing-view]')];
    const viewIds = new Set(views.map((view) => view.dataset.landingView));
    const panels = [...document.querySelectorAll('.landing-action-panel')];

    function setOpen(id) {
      for (const button of buttons) {
        const open = button.dataset.landingAction === id;
        button.setAttribute('aria-expanded', open ? 'true' : 'false');
      }
      for (const panel of panels) panel.hidden = panel.id !== `landing-panel-${id}`;
      return panels.find((panel) => !panel.hidden);
    }

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

    function scrollToView(id, panel) {
      const target = panel ?? views.find((view) => view.dataset.landingView === id);
      if (!target) return;
      const behavior = window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth';
      requestAnimationFrame(() => requestAnimationFrame(() => {
        target.scrollIntoView({ behavior, block: 'start' });
      }));
    }

    function selectView(id, updateHistory) {
      const panel = setOpen(id);
      if (updateHistory) updateUrl(id);
      scrollToView(id, panel);
    }

    for (const button of buttons) {
      button.addEventListener('click', () => {
        const id = button.dataset.landingAction;
        if (button.getAttribute('aria-expanded') === 'true') {
          setOpen(undefined);
          updateUrl(undefined);
          return;
        }
        selectView(id, true);
      });
    }

    for (const view of views.filter((candidate) => !candidate.dataset.landingAction)) {
      const selectUnavailable = () => selectView(view.dataset.landingView, true);
      view.addEventListener('click', selectUnavailable);
      view.addEventListener('keydown', (event) => {
        if (event.key !== 'Enter' && event.key !== ' ') return;
        event.preventDefault();
        selectUnavailable();
      });
    }

    window.addEventListener('popstate', () => {
      const id = urlView();
      if (id) selectView(id, false);
      else setOpen(undefined);
    });

    const initialView = urlView();
    if (initialView) selectView(initialView, false);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', setupLandingActions);
  } else {
    setupLandingActions();
  }
})();
