/* Compiler-derived types are embedded in the page; this makes no requests. */
(() => {
  const panel = document.createElement("div");
  panel.className = "lean-type-tooltip";
  panel.id = "lean-type-tooltip";
  panel.setAttribute("role", "dialog");
  panel.setAttribute("aria-label", "Lean type");
  panel.hidden = true;
  document.body.append(panel);
  let active = null, pinned = false, hideTimer;
  const target = event => event.target.closest?.("[data-lean-type]");
  const hide = () => {
    clearTimeout(hideTimer);
    active?.removeAttribute("aria-describedby");
    active?.removeAttribute("aria-expanded");
    active = null; pinned = false; panel.hidden = true;
  };
  const place = () => {
    if (!active || !active.isConnected) return hide();
    const node = active.getBoundingClientRect(), gap = 8;
    const width = panel.offsetWidth, height = panel.offsetHeight;
    const left = Math.max(gap, Math.min(node.left, innerWidth - width - gap));
    const top = node.bottom + gap + height <= innerHeight - gap ? node.bottom + gap : Math.max(gap, node.top - height - gap);
    panel.style.left = `${left}px`; panel.style.top = `${top}px`;
  };
  const show = (node, pin = false) => {
    if (pinned && !pin) return;
    clearTimeout(hideTimer);
    if (active !== node) {
      active?.removeAttribute("aria-describedby"); active?.removeAttribute("aria-expanded");
      const text = node.dataset.leanType;
      let links;
      try { links = JSON.parse(node.dataset.leanTypeLinks || "[]"); } catch { links = []; }
      panel.replaceChildren();
      let end = 0;
      for (const link of links) {
        if (!Number.isInteger(link.start) || !Number.isInteger(link.end) || link.start < end ||
            link.end <= link.start || link.end > text.length || typeof link.href !== "string") continue;
        const url = new URL(link.href, document.baseURI);
        if (url.protocol !== "https:" && url.protocol !== "http:") continue;
        panel.append(document.createTextNode(text.slice(end, link.start)));
        const anchor = document.createElement("a");
        anchor.className = "lean-type-link"; anchor.href = link.href;
        anchor.textContent = text.slice(link.start, link.end); panel.append(anchor); end = link.end;
      }
      panel.append(document.createTextNode(text.slice(end)));
    }
    active = node; pinned = pin; panel.hidden = false;
    node.setAttribute("aria-describedby", panel.id); place();
    node.setAttribute("aria-expanded", "true");
  };
  const scheduleHide = () => {
    clearTimeout(hideTimer);
    hideTimer = setTimeout(() => {
      if (!pinned && active !== document.activeElement && !panel.contains(document.activeElement)) hide();
    }, 180);
  };
  document.addEventListener("pointerover", event => { const node = target(event); if (node) show(node); });
  document.addEventListener("pointerout", event => {
    if (target(event) && !active?.contains(event.relatedTarget) && !panel.contains(event.relatedTarget)) scheduleHide();
  });
  document.addEventListener("focusin", event => {
    const node = target(event);
    if (node) show(node);
    else if (!pinned && !panel.contains(event.target)) hide();
  });
  document.addEventListener("focusout", event => { if (target(event)) scheduleHide(); });
  document.addEventListener("click", event => {
    if (panel.contains(event.target)) return;
    const node = target(event);
    if (node) {
      // Preserve modifier-click navigation for identifiers with a destination.
      if (node.matches("a[href]") && (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey)) return;
      event.preventDefault(); show(node, true);
    } else hide();
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Escape") {
      const node = active, restore = panel.contains(document.activeElement);
      hide();
      if (restore) { node?.focus(); hide(); }
    }
    const node = target(event);
    if (node && (event.key === "Enter" || event.key === " ")) {
      event.preventDefault(); show(node, true);
    }
    if (node === active && pinned && event.key === "Tab" && !event.shiftKey) {
      const first = panel.querySelector("a");
      if (first) { event.preventDefault(); first.focus(); }
    }
  });
  panel.addEventListener("pointerenter", () => clearTimeout(hideTimer));
  panel.addEventListener("pointerleave", scheduleHide);
  document.addEventListener("scroll", event => { if (!panel.contains(event.target)) { if (pinned) place(); else hide(); } }, true);
  window.addEventListener("resize", () => { if (pinned) place(); else hide(); });
})();
