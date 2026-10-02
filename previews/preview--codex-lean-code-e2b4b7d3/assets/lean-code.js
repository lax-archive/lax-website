/* Compiler-derived types are embedded in the page; this makes no requests. */
(() => {
  const panel = document.createElement("div");
  panel.className = "lean-type-tooltip";
  panel.id = "lean-type-tooltip";
  panel.setAttribute("role", "dialog");
  panel.setAttribute("aria-label", "Lean type");
  panel.hidden = true;
  document.body.append(panel);
  const destination = document.createElement("div");
  destination.className = "lean-link-tooltip";
  destination.setAttribute("role", "tooltip");
  destination.hidden = true;
  document.body.append(destination);
  const hideDestination = () => { destination.hidden = true; };
  const showDestination = node => {
    node ??= active;
    const label = node?.dataset.destination ?? node?.dataset.leanDestination;
    if (!label || panel.hidden) return hideDestination();
    destination.textContent = label;
    destination.hidden = false;
    const gap = 6, edge = 8, height = destination.offsetHeight;
    let bounds = panel.getBoundingClientRect();
    let top = bounds.top - gap - height;
    if (top < edge) {
      // Reserve room above the type rather than overlaying its text.
      panel.style.top = `${edge + height + gap}px`;
      bounds = panel.getBoundingClientRect();
      top = bounds.top - gap - height;
    }
    destination.style.top = `${top}px`;
    destination.style.left = `${Math.max(edge, Math.min(node.getBoundingClientRect().left, innerWidth - destination.offsetWidth - edge))}px`;
  };
  let active = null, pinned = false, hideTimer;
  let enabled = true;
  try { enabled = localStorage.getItem("lax-show-types") !== "false"; } catch { /* Storage can be disabled. */ }
  const target = event => enabled ? event.target.closest?.("[data-lean-type]") : null;
  const hide = () => {
    hideDestination();
    clearTimeout(hideTimer);
    active?.removeAttribute("aria-describedby");
    active?.removeAttribute("aria-expanded");
    active = null; pinned = false; panel.hidden = true;
  };
  const place = () => {
    hideDestination();
    if (!active || !active.isConnected) return hide();
    const node = active.getBoundingClientRect(), gap = 8;
    const width = panel.offsetWidth, height = panel.offsetHeight;
    const left = Math.max(gap, Math.min(node.left, innerWidth - width - gap));
    const top = node.bottom + gap + height <= innerHeight - gap ? node.bottom + gap : Math.max(gap, node.top - height - gap);
    panel.style.left = `${left}px`; panel.style.top = `${top}px`;
    showDestination(active);
  };
  const show = (node, pin = false) => {
    if (!enabled) return;
    if (pinned && !pin) return;
    clearTimeout(hideTimer);
    if (active !== node) {
      hideDestination();
      active?.removeAttribute("aria-describedby"); active?.removeAttribute("aria-expanded");
      const text = node.dataset.leanType;
      let links;
      try { links = JSON.parse(node.dataset.leanTypeLinks || "[]"); } catch { links = []; }
      panel.replaceChildren();
      const signature = document.createElement("div");
      signature.className = "lean-type-signature";
      panel.append(signature);
      let end = 0;
      for (const link of links) {
        if (!Number.isInteger(link.start) || !Number.isInteger(link.end) || link.start < end ||
            link.end <= link.start || link.end > text.length || typeof link.href !== "string") continue;
        const url = new URL(link.href, document.baseURI);
        if (url.protocol !== "https:" && url.protocol !== "http:") continue;
        signature.append(document.createTextNode(text.slice(end, link.start)));
        const anchor = document.createElement("a");
        anchor.className = "lean-type-link"; anchor.href = link.href;
        if (typeof link.title === "string") {
          anchor.dataset.destination = link.title;
          anchor.setAttribute("aria-label", `${text.slice(link.start, link.end)}, ${link.title}`);
        }
        anchor.textContent = text.slice(link.start, link.end); signature.append(anchor); end = link.end;
      }
      signature.append(document.createTextNode(text.slice(end)));
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
  const applyPreference = () => {
    if (!enabled) hide();
    document.documentElement.classList.toggle("lean-types-disabled", !enabled);
    document.querySelectorAll("[data-type-hover-toggle]").forEach(input => { input.checked = enabled; });
    document.querySelectorAll(".lean-typed-identifier").forEach(node => {
      node.tabIndex = enabled ? 0 : -1;
      if (enabled) node.setAttribute("role", "button");
      else node.removeAttribute("role");
    });
    document.querySelectorAll("a[data-lean-type][data-lean-destination]").forEach(node => {
      if (enabled) node.removeAttribute("title");
      else node.title = node.dataset.leanDestination;
    });
  };
  document.querySelectorAll("[data-type-hover-toggle]").forEach(input => {
    input.addEventListener("change", () => {
      enabled = input.checked;
      try { localStorage.setItem("lax-show-types", String(enabled)); } catch { /* Keep the page preference. */ }
      applyPreference();
    });
  });
  applyPreference();
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
    if (panel.contains(event.target)) {
      if (event.target.closest?.("a[href]")) hide();
      else { pinned = true; clearTimeout(hideTimer); }
      return;
    }
    const node = target(event);
    if (node) {
      // Source identifiers with a destination keep ordinary link navigation.
      if (node.matches("a[href]")) return;
      event.preventDefault();
      if (node === active && pinned) hide();
      else show(node, true);
    } else hide();
  });
  document.addEventListener("keydown", event => {
    if (event.key === "Escape") {
      const node = active, restore = panel.contains(document.activeElement);
      hide();
      if (restore) { node?.focus(); hide(); }
    }
    const node = target(event);
    if (node && (event.key === " " || (event.key === "Enter" && !node.matches("a[href]")))) {
      event.preventDefault(); show(node, true);
    }
    if (node === active && pinned && event.key === "Tab" && !event.shiftKey) {
      const first = panel.querySelector("a");
      if (first) { event.preventDefault(); first.focus(); }
    }
  });
  panel.addEventListener("pointerenter", () => clearTimeout(hideTimer));
  panel.addEventListener("pointerleave", scheduleHide);
  const destinationTarget = event => event.target.closest?.("a[data-destination]");
  panel.addEventListener("pointerover", event => showDestination(destinationTarget(event)));
  panel.addEventListener("pointerout", () => showDestination(active));
  panel.addEventListener("focusin", event => showDestination(destinationTarget(event)));
  panel.addEventListener("focusout", () => showDestination(active));
  document.addEventListener("scroll", event => { hideDestination(); if (!panel.contains(event.target)) { if (pinned) place(); else hide(); } }, true);
  window.addEventListener("resize", () => { if (pinned) place(); else hide(); });
})();
