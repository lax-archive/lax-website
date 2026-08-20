// Keep proof actions aligned with their declaration row without placing them
// inside the horizontally scrollable Lean table. When the page has enough
// room to the right, the action moves outside the source block.
(() => {
  const positionAll = () => {
    const groups = new Map();
    document.querySelectorAll('.source-proof-rail[data-source-line], .source-review-rail[data-source-line]').forEach((rail) => {
      const shell = rail.closest('.inline-contract-shell');
      const row = document.getElementById(rail.dataset.sourceLine);
      if (!shell || !row) return;
      const key = `${rail.dataset.sourceLine}:${[...document.querySelectorAll('.inline-contract-shell')].indexOf(shell)}`;
      const group = groups.get(key) || { shell, row, rails: [] };
      group.rails.push(rail);
      groups.set(key, group);
    });
    for (const { shell, row, rails } of groups.values()) {
      const shellRect = shell.getBoundingClientRect();
      const rowRect = row.getBoundingClientRect();
      const totalWidth = rails.reduce((sum, rail) => sum + rail.offsetWidth, 0) + Math.max(0, rails.length - 1) * 6;
      const outside = document.documentElement.clientWidth - shellRect.right >= totalWidth + 12;
      let offset = 0;
      for (const rail of rails) {
        rail.style.top = `${rowRect.top - shellRect.top + rowRect.height / 2}px`;
        rail.classList.toggle('outside', outside);
        if (outside) {
          rail.style.left = `calc(100% + ${10 + offset}px)`;
          rail.style.right = 'auto';
        } else {
          rail.style.right = `${10 + offset}px`;
          rail.style.left = 'auto';
        }
        offset += rail.offsetWidth + 6;
      }
    }
  };
  positionAll();
  window.addEventListener('resize', positionAll);
  window.addEventListener('LAX::source-rails-changed', positionAll);
  document.fonts?.ready.then(positionAll);

  const main = document.getElementById('main');
  if (main && 'ResizeObserver' in window) new ResizeObserver(positionAll).observe(main);
})();
