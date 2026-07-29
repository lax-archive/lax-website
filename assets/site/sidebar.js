// Sidebar behavior: mobile drawer toggle and entry filtering. All data is in
// the DOM (data-search / data-type attributes); nothing is fetched.
(() => {
  function isMobile() {
    return window.matchMedia('(max-width: 900px)').matches;
  }

  function applyFilters() {
    const list = document.getElementById('entry-list');
    if (!list) return;
    const searchEl = document.getElementById('filter-search');
    const typeEl = document.getElementById('filter-type');
    const search = searchEl ? searchEl.value.trim().toLowerCase() : '';
    const type = typeEl ? typeEl.value : 'all';
    let visible = 0;
    list.querySelectorAll('li[data-search]').forEach((li) => {
      let hidden = false;
      if (search && !li.dataset.search.includes(search)) hidden = true;
      if (!hidden && type !== 'all' && li.dataset.type !== type) hidden = true;
      li.hidden = hidden;
      if (!hidden) visible += 1;
    });
    // A group heading (Concepts / Proofs) shows only while its group does.
    list.querySelectorAll('li.entry-heading').forEach((heading) => {
      let any = false;
      for (let el = heading.nextElementSibling; el && !el.classList.contains('entry-heading'); el = el.nextElementSibling) {
        if (el.dataset.search !== undefined && !el.hidden) { any = true; break; }
      }
      heading.hidden = !any;
    });
    const empty = document.getElementById('entry-list-empty');
    if (empty) empty.hidden = visible > 0;
  }

  function setupFilters() {
    const search = document.getElementById('filter-search');
    const type = document.getElementById('filter-type');
    if (search) search.addEventListener('input', applyFilters);
    if (type) type.addEventListener('change', applyFilters);
  }

  function setupToggle() {
    const sidebar = document.getElementById('sidebar');
    const backdrop = document.getElementById('sidebar-backdrop');
    const shell = document.getElementById('content-shell');
    const toggleBtn = document.getElementById('sidebar-toggle');
    if (!sidebar || !toggleBtn) return;

    function visible() {
      if (isMobile()) return sidebar.classList.contains('open');
      return !shell || !shell.classList.contains('sidebar-hidden');
    }
    function setVisible(v) {
      if (isMobile()) {
        sidebar.classList.toggle('open', v);
        if (backdrop) backdrop.classList.toggle('open', v);
      } else if (shell) {
        shell.classList.toggle('sidebar-hidden', !v);
      }
      toggleBtn.setAttribute('aria-expanded', v ? 'true' : 'false');
    }
    toggleBtn.addEventListener('click', () => setVisible(!visible()));
    if (backdrop) backdrop.addEventListener('click', () => setVisible(false));
    document.addEventListener('keydown', (event) => {
      if (event.key === 'Escape' && isMobile() && visible()) setVisible(false);
    });
    if (isMobile()) {
      toggleBtn.setAttribute('aria-expanded', 'false');
      requestAnimationFrame(() => requestAnimationFrame(() => {
        sidebar.classList.add('ready');
        if (backdrop) backdrop.classList.add('ready');
      }));
    } else {
      toggleBtn.setAttribute('aria-expanded', 'true');
    }
  }

  function init() {
    setupFilters();
    applyFilters();
    setupToggle();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
