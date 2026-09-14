/* The original landing page's concept/proof flip, shared with About. */
(() => {
  'use strict';

  for (const card of document.querySelectorAll('[data-proof-flip]')) {
    const precisePointer = window.matchMedia('(hover: hover) and (pointer: fine)');
    let pinned = false;

    function setFlipped(flipped) {
      card.classList.toggle('is-flipped', flipped);
      card.setAttribute('aria-pressed', String(flipped));
      card.setAttribute('aria-label', flipped
        ? 'Proof excerpt: Erdős–Hajnal for the five-cycle. Activate to return to its concept file.'
        : 'Concept file: Erdős–Hajnal for the five-cycle. Hover or activate to see a proof excerpt.');
    }

    card.addEventListener('pointerenter', () => {
      if (precisePointer.matches) setFlipped(true);
    });
    card.addEventListener('pointerleave', () => {
      if (precisePointer.matches) setFlipped(pinned);
    });
    card.addEventListener('click', (event) => {
      // Pointer hover turns the card temporarily; touch and keyboard pin a side.
      if (precisePointer.matches && event.detail !== 0) return;
      pinned = !pinned;
      setFlipped(pinned);
    });
    card.addEventListener('keydown', (event) => {
      if (event.key !== 'Escape') return;
      event.preventDefault();
      pinned = false;
      setFlipped(false);
    });
  }
})();
