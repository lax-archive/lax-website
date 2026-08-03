// Landing-page action cards scroll to their always-visible sections and keep
// shareable ?view= URLs in sync.
(() => {
  const RESET_DELAY = 2200;

  function legacyCopy(text) {
    const field = document.createElement('textarea');
    field.value = text;
    field.setAttribute('readonly', '');
    field.style.position = 'fixed';
    field.style.opacity = '0';
    document.body.append(field);
    field.select();
    const copied = document.execCommand('copy');
    field.remove();
    if (!copied) throw new Error('copy command failed');
  }

  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      await navigator.clipboard.writeText(text);
      return;
    }
    legacyCopy(text);
  }

  function setupPromptCopy() {
    const button = document.querySelector('[data-copy-prompt]');
    if (!button) return;
    const prompt = document.getElementById(button.getAttribute('aria-controls'));
    const status = button.parentElement.querySelector('.prompt-copy-status');
    if (!prompt || !status) return;
    let resetTimer;

    button.addEventListener('click', async () => {
      clearTimeout(resetTimer);
      try {
        await copyText(prompt.textContent);
        button.classList.add('is-copied');
        button.setAttribute('aria-label', 'Prompt copied');
        button.title = 'Copied';
        status.textContent = 'Copied';
      } catch {
        button.classList.remove('is-copied');
        button.setAttribute('aria-label', 'Could not copy prompt');
        button.title = 'Could not copy';
        status.textContent = 'Select and copy manually';
      }

      resetTimer = setTimeout(() => {
        button.classList.remove('is-copied');
        button.setAttribute('aria-label', 'Copy prompt to clipboard');
        button.title = 'Copy prompt';
        status.textContent = '';
      }, RESET_DELAY);
    });
  }

  function setupLandingActions() {
    const buttons = [...document.querySelectorAll('[data-landing-action]')];
    if (!buttons.length) return;
    const views = [...document.querySelectorAll('[data-landing-view]')];
    const viewIds = new Set(views.map((view) => view.dataset.landingView));

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
      const target = document.getElementById(`landing-panel-${id}`)
        ?? views.find((view) => view.dataset.landingView === id);
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
    });

    const initialView = urlView();
    if (initialView) selectView(initialView, false);
  }

  function setupLanding() {
    setupLandingActions();
    setupPromptCopy();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', setupLanding);
  else setupLanding();
})();
