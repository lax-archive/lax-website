/* Compiler-derived types are embedded in the page; this makes no requests. */
(() => {
  const panel = document.createElement("div");
  panel.className = "lean-type-tooltip";
  panel.id = "lean-type-tooltip";
  panel.setAttribute("role", "tooltip");
  panel.hidden = true;
  document.body.append(panel);
  let active = null, hideTimer;
  const target = event => event.target.closest?.("[data-lean-type]");
  const hide = () => {
    clearTimeout(hideTimer);
    active?.removeAttribute("aria-describedby"); active = null; panel.hidden = true;
  };
  const place = () => {
    if (!active || !active.isConnected) return hide();
    const node = active.getBoundingClientRect(), gap = 8;
    const width = panel.offsetWidth, height = panel.offsetHeight;
    const left = Math.max(gap, Math.min(node.left, innerWidth - width - gap));
    const top = node.bottom + gap + height <= innerHeight - gap ? node.bottom + gap : Math.max(gap, node.top - height - gap);
    panel.style.left = `${left}px`; panel.style.top = `${top}px`;
  };
  const show = node => {
    clearTimeout(hideTimer);
    if (active !== node) active?.removeAttribute("aria-describedby");
    active = node; panel.textContent = node.dataset.leanType; panel.hidden = false;
    node.setAttribute("aria-describedby", panel.id); place();
  };
  const scheduleHide = () => {
    clearTimeout(hideTimer);
    hideTimer = setTimeout(() => { if (active !== document.activeElement) hide(); }, 180);
  };
  document.addEventListener("pointerover", event => { const node = target(event); if (node) show(node); });
  document.addEventListener("pointerout", event => {
    if (target(event) && !active?.contains(event.relatedTarget) && !panel.contains(event.relatedTarget)) scheduleHide();
  });
  document.addEventListener("focusin", event => { const node = target(event); if (node) show(node); else hide(); });
  document.addEventListener("focusout", event => { if (target(event)) scheduleHide(); });
  document.addEventListener("keydown", event => { if (event.key === "Escape") hide(); });
  panel.addEventListener("pointerenter", () => clearTimeout(hideTimer));
  panel.addEventListener("pointerleave", scheduleHide);
  document.addEventListener("scroll", event => { if (event.target !== panel) hide(); }, true);
  window.addEventListener("resize", hide);
})();
