// Accessible operating-system tabs shared by the front page and setup guide.
(() => {
  function setupTabs() {
    for (const root of document.querySelectorAll('[data-setup-tabs]')) {
      const tabs = [...root.querySelectorAll('[role="tab"]')];
      const panels = tabs.map((tab) => document.getElementById(tab.getAttribute('aria-controls')));

      function select(index, focus) {
        tabs.forEach((tab, tabIndex) => {
          const selected = tabIndex === index;
          tab.setAttribute('aria-selected', String(selected));
          tab.tabIndex = selected ? 0 : -1;
          if (panels[tabIndex]) panels[tabIndex].hidden = !selected;
        });
        if (focus) tabs[index].focus();
      }

      tabs.forEach((tab, index) => {
        tab.addEventListener('click', () => select(index, false));
        tab.addEventListener('keydown', (event) => {
          let next;
          if (event.key === 'ArrowRight') next = (index + 1) % tabs.length;
          else if (event.key === 'ArrowLeft') next = (index - 1 + tabs.length) % tabs.length;
          else if (event.key === 'Home') next = 0;
          else if (event.key === 'End') next = tabs.length - 1;
          else return;
          event.preventDefault();
          select(next, true);
        });
      });
    }
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', setupTabs);
  else setupTabs();
})();
