// Keep proof actions aligned with their declaration row without placing them
// inside the horizontally scrollable Lean table. When the page has enough
// room to the right, the action moves outside the source block.
(() => {
  const rails = [...document.querySelectorAll('.source-proof-rail[data-source-line]')];
  if (!rails.length) return;

  function positionRail(rail) {
    const shell = rail.closest('.inline-contract-shell');
    const row = document.getElementById(rail.dataset.sourceLine);
    if (!shell || !row) return;

    const shellRect = shell.getBoundingClientRect();
    const rowRect = row.getBoundingClientRect();
    rail.style.top = `${rowRect.top - shellRect.top + rowRect.height / 2}px`;

    const room = document.documentElement.clientWidth - shellRect.right;
    rail.classList.toggle('outside', room >= rail.offsetWidth + 12);
  }

  const positionAll = () => rails.forEach(positionRail);
  positionAll();
  window.addEventListener('resize', positionAll);
  document.fonts?.ready.then(positionAll);

  const main = document.getElementById('main');
  if (main && 'ResizeObserver' in window) new ResizeObserver(positionAll).observe(main);
})();
