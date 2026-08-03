// Landing-page action cards disclose one focused panel at a time. The
// content is already in the static HTML; this only manages visibility and
// accessible expanded state.
(() => {
  function setupLandingActions() {
    const buttons = [...document.querySelectorAll('[data-landing-action]')];
    if (!buttons.length) return;
    const panels = [...document.querySelectorAll('.landing-action-panel')];

    function setOpen(id) {
      for (const button of buttons) {
        const open = button.dataset.landingAction === id;
        button.setAttribute('aria-expanded', open ? 'true' : 'false');
      }
      for (const panel of panels) panel.hidden = panel.id !== `landing-panel-${id}`;
      return panels.find((panel) => !panel.hidden);
    }

    for (const button of buttons) {
      button.addEventListener('click', () => {
        const id = button.dataset.landingAction;
        const panel = setOpen(button.getAttribute('aria-expanded') === 'true' ? undefined : id);
        if (!panel) return;
        const behavior = window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth';
        requestAnimationFrame(() => requestAnimationFrame(() => {
          panel.scrollIntoView({ behavior, block: 'start' });
        }));
      });
    }
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', setupLandingActions);
  } else {
    setupLandingActions();
  }
})();
