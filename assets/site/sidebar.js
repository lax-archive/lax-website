// Sidebar behavior: mobile drawer toggle and entry filtering. All data is in
// the DOM (data-search / data-type attributes); nothing is fetched.
(() => {
  function isMobile() {
    return window.matchMedia('(max-width: 900px)').matches;
  }

  function words(value) {
    const normalized = value.normalize('NFKD').replace(/\p{M}/gu, '').toLocaleLowerCase();
    return normalized.match(/[\p{L}\p{N}]+/gu) || [];
  }

  function containsWord(haystack, needle) {
    return haystack.some((word) => word.includes(needle));
  }

  function stateRank(state) {
    if (state === 'registered') return 0;
    if (state === 'draft') return 1;
    return 2;
  }

  function filterList(list, search, type, emptyId) {
    const query = words(search);
    const rows = [...list.querySelectorAll('li[data-search], li[data-search-title]')];
    const titleHits = new Map();
    let visible = 0;
    rows.forEach((li) => {
      let hidden = false;
      if (li.dataset.searchTitle !== undefined) {
        const title = words(li.dataset.searchTitle);
        const concepts = words(li.dataset.searchConcepts || '');
        titleHits.set(li, query.filter((word) => containsWord(title, word)).length);
        if (query.some((word) => !containsWord(title, word) && !containsWord(concepts, word))) hidden = true;
      } else if (search && !li.dataset.search.includes(search)) {
        hidden = true;
      }
      if (!hidden && type !== 'all' && li.dataset.type !== type) hidden = true;
      li.hidden = hidden;
      if (!hidden) visible += 1;
    });

    // The index rows carry two separate search fields. Keep registered work
    // before drafts, then prefer rows with more query words in their title.
    if (rows.some((row) => row.dataset.searchTitle !== undefined)) {
      rows.sort((a, b) => stateRank(a.dataset.state) - stateRank(b.dataset.state)
        || (titleHits.get(b) || 0) - (titleHits.get(a) || 0)
        || Number(a.dataset.searchOrder) - Number(b.dataset.searchOrder));
      const empty = document.getElementById(emptyId);
      rows.forEach((row) => list.insertBefore(row, empty));
    }

    const empty = document.getElementById(emptyId);
    if (empty) empty.hidden = visible > 0;
  }

  function applyFilters() {
    const list = document.getElementById('entry-list');
    if (!list) return;
    const searchEl = document.getElementById('filter-search');
    const typeEl = document.getElementById('filter-type');
    const search = searchEl ? searchEl.value.trim().toLowerCase() : '';
    const type = typeEl ? typeEl.value : 'all';
    filterList(list, search, type, 'entry-list-empty');
    const submissions = document.getElementById('submissions-list');
    if (submissions) filterList(submissions, search, 'all', 'submissions-list-empty');
    // A group heading (Concepts / Proofs) shows only while its group does.
    list.querySelectorAll('li.entry-heading').forEach((heading) => {
      let any = false;
      for (let el = heading.nextElementSibling; el && !el.classList.contains('entry-heading'); el = el.nextElementSibling) {
        if (el.dataset.search !== undefined && !el.hidden) { any = true; break; }
      }
      heading.hidden = !any;
    });
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
    const header = document.querySelector('.site-header');
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
        if (header) header.classList.toggle('sidebar-hidden', !v);
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
