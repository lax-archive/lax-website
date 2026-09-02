// Sidebar behavior: mobile drawer toggle and entry filtering. All data is in
// the DOM (data-search / data-type attributes); nothing is fetched.
(() => {
  let searchHasSelectedRead = false;
  let selectedTag = '';

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

  function filterList(list, search, type, emptyId, tag = '') {
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
      if (!hidden && tag && li.dataset.tags !== undefined && !li.dataset.tags.includes(`|${tag}|`)) hidden = true;
      li.hidden = hidden;
      if (!hidden) visible += 1;
    });

    // The index rows carry two separate search fields. Keep registered work
    // before drafts, then prefer rows with more query words in their title.
    // Each row stays below its group heading while filtering.
    if (rows.some((row) => row.dataset.searchTitle !== undefined)) {
      rows.sort((a, b) => stateRank(a.dataset.state) - stateRank(b.dataset.state)
        || (titleHits.get(b) || 0) - (titleHits.get(a) || 0)
        || Number(a.dataset.searchOrder) - Number(b.dataset.searchOrder));
      const empty = document.getElementById(emptyId);
      const draftHeading = list.querySelector('[data-entry-group="draft"]');
      if (draftHeading) {
        const boundary = (row) => {
          if (row.dataset.state === 'draft') return empty;
          return draftHeading;
        };
        rows.forEach((row) => list.insertBefore(row, boundary(row)));
      } else {
        rows.forEach((row) => list.insertBefore(row, empty));
      }
    }

    const empty = document.getElementById(emptyId);
    if (empty) empty.hidden = visible > 0;
    return visible;
  }

  function updateTagStatus(visible) {
    const status = document.getElementById('tag-results-status');
    if (!status) return;
    const active = document.querySelector(`[data-tag-filter="${CSS.escape(selectedTag)}"]`);
    const label = active?.querySelector('span')?.textContent ?? selectedTag;
    const search = document.getElementById('filter-search')?.value.trim();
    const suffix = search ? ' matching your search' : '';
    status.textContent = selectedTag
      ? `Showing ${visible} ${visible === 1 ? 'submission' : 'submissions'} tagged “${label}”${suffix}.`
      : `Showing all ${visible} ${visible === 1 ? 'submission' : 'submissions'}${suffix}.`;
  }

  function applySidebarFilters() {
    const list = document.getElementById('entry-list');
    if (!list) return;
    const searchEl = document.getElementById('filter-search');
    const typeEl = document.getElementById('filter-type');
    const search = searchEl ? searchEl.value.trim().toLowerCase() : '';
    const type = typeEl ? typeEl.value : 'all';
    filterList(list, search, type, 'entry-list-empty');
    const openProblems = document.getElementById('open-problems-list');
    if (openProblems) {
      filterList(openProblems, search, type, 'open-problems-list-empty');
    }

    // A group heading shows only while its group has a visible row.
    list.querySelectorAll('li.entry-heading').forEach((heading) => {
      let any = false;
      for (let el = heading.nextElementSibling; el && !el.classList.contains('entry-heading'); el = el.nextElementSibling) {
        if ((el.dataset.search !== undefined || el.dataset.searchTitle !== undefined) && !el.hidden) {
          any = true;
          break;
        }
      }
      heading.hidden = !any;
    });
  }

  function applySubmissionFilters() {
    const submissions = document.getElementById('submissions-list');
    if (!submissions) return;
    const searchEl = document.getElementById('filter-search');
    const search = searchEl?.value.trim().toLowerCase() ?? '';
    const randomSubmission = document.querySelector('.random-submission');
    if (randomSubmission) randomSubmission.hidden = Boolean(searchEl?.value.length);
    const visible = filterList(submissions, search, 'all', 'submissions-list-empty', selectedTag);
    updateTagStatus(visible);
    // Search results live in the always-visible Read section. Move there
    // once when a visitor begins a new search, not on every keystroke.
    const readAction = document.querySelector('[data-landing-action="read"]');
    if (search && !searchHasSelectedRead) {
      readAction?.click();
      searchHasSelectedRead = true;
    } else if (!search) {
      searchHasSelectedRead = false;
    }
  }

  function applyFilters() {
    applySidebarFilters();
    applySubmissionFilters();
  }

  function setupFilters() {
    const search = document.getElementById('filter-search');
    const type = document.getElementById('filter-type');
    if (search) search.addEventListener('input', applyFilters);
    if (type) type.addEventListener('change', applyFilters);
  }

  function setupRandomSubmission() {
    const link = document.querySelector('[data-random-submission-link]');
    const candidates = [...document.querySelectorAll('[data-random-submission-candidate]')];
    if (!link || !candidates.length) return;
    const selected = candidates[Math.floor(Math.random() * candidates.length)];
    link.href = selected.href;
    link.replaceChildren(...[...selected.childNodes].map((node) => node.cloneNode(true)));
  }

  function setupTagFilters() {
    const buttons = [...document.querySelectorAll('[data-tag-filter]')];
    if (!buttons.length) return;
    const list = document.querySelector('.tag-chip-list');
    const keys = new Set(buttons.map((button) => button.dataset.tagFilter));

    function fitTagRows() {
      if (!list) return;
      buttons.forEach((button) => { button.hidden = false; });
      const tops = buttons.map((button) => button.offsetTop);
      const rows = [...new Set(tops)].sort((a, b) => a - b);
      const lastVisibleTop = rows[2] ?? Number.POSITIVE_INFINITY;
      buttons.forEach((button, index) => { button.hidden = tops[index] > lastVisibleTop; });
    }

    let resizeFrame;
    function queueTagFit() {
      cancelAnimationFrame(resizeFrame);
      resizeFrame = requestAnimationFrame(fitTagRows);
    }

    function urlTag() {
      const tag = new URLSearchParams(window.location.search).get('tag') ?? '';
      return keys.has(tag) ? tag : '';
    }

    function updateUrl(tag) {
      const url = new URL(window.location.href);
      if (tag) url.searchParams.set('tag', tag);
      else url.searchParams.delete('tag');
      url.searchParams.set('view', 'read');
      window.history.pushState(null, '', `${url.pathname}${url.search}${url.hash}`);
    }

    function selectTag(tag, updateHistory) {
      selectedTag = keys.has(tag) ? tag : '';
      buttons.forEach((button) => {
        button.setAttribute('aria-pressed', button.dataset.tagFilter === selectedTag ? 'true' : 'false');
      });
      if (updateHistory) updateUrl(selectedTag);
      applySubmissionFilters();
    }

    buttons.forEach((button) => {
      button.addEventListener('click', () => {
        const tag = button.dataset.tagFilter;
        selectTag(tag === selectedTag ? '' : tag, true);
      });
    });
    window.addEventListener('popstate', () => selectTag(urlTag(), false));
    selectedTag = urlTag();
    buttons.forEach((button) => {
      button.setAttribute('aria-pressed', button.dataset.tagFilter === selectedTag ? 'true' : 'false');
    });
    fitTagRows();
    window.addEventListener('resize', queueTagFit);
    document.fonts?.ready.then(queueTagFit);
  }

  function setupEntryTooltips() {
    const links = [...document.querySelectorAll('#entry-list .entry-link[data-full-title]')];
    if (!links.length) return;
    const tooltip = document.createElement('div');
    tooltip.id = 'sidebar-entry-tooltip';
    tooltip.className = 'sidebar-entry-tooltip';
    tooltip.setAttribute('role', 'tooltip');
    tooltip.hidden = true;
    document.body.append(tooltip);
    let activeLink;

    function hide() {
      if (activeLink) activeLink.removeAttribute('aria-describedby');
      activeLink = undefined;
      tooltip.hidden = true;
    }

    function show(link) {
      if (isMobile()) return;
      const label = link.querySelector('.entry-label-text');
      if (!label || label.scrollWidth <= label.clientWidth + 1) {
        hide();
        return;
      }
      if (activeLink && activeLink !== link) activeLink.removeAttribute('aria-describedby');
      activeLink = link;
      tooltip.textContent = link.dataset.fullTitle;
      tooltip.hidden = false;
      link.setAttribute('aria-describedby', tooltip.id);
      const anchor = link.getBoundingClientRect();
      const top = Math.min(
        Math.max(anchor.top + anchor.height / 2 - tooltip.offsetHeight / 2, 8),
        window.innerHeight - tooltip.offsetHeight - 8,
      );
      tooltip.style.left = `${anchor.right + 9}px`;
      tooltip.style.top = `${top}px`;
    }

    links.forEach((link) => {
      link.addEventListener('mouseenter', () => show(link));
      link.addEventListener('mouseleave', hide);
      link.addEventListener('focus', () => show(link));
      link.addEventListener('blur', hide);
    });
    const sidebar = document.getElementById('sidebar');
    if (sidebar) sidebar.addEventListener('scroll', hide, { passive: true });
    window.addEventListener('resize', hide);
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
      // A page may ship with the sidebar already collapsed (the paper page).
      toggleBtn.setAttribute('aria-expanded', visible() ? 'true' : 'false');
    }
  }

  function init() {
    setupRandomSubmission();
    setupFilters();
    setupTagFilters();
    applyFilters();
    setupEntryTooltips();
    setupToggle();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
