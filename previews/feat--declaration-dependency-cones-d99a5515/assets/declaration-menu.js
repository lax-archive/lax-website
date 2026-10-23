/* Declaration actions share one menu, including source inside paper cards. */
(() => {
  const menu = document.createElement("div");
  menu.id = "lean-declaration-menu";
  menu.className = "lean-declaration-menu";
  menu.setAttribute("role", "menu");
  menu.setAttribute("aria-label", "Dependency cone");
  menu.hidden = true;
  const download = document.createElement("a"), live = document.createElement("a");
  download.setAttribute("role", "menuitem");
  download.textContent = "Download dependency cone";
  live.setAttribute("role", "menuitem");
  live.textContent = "Open dependency cone in live-lean";
  live.target = "_blank"; live.rel = "noopener noreferrer";
  menu.append(download, live); document.body.append(menu);
  let active;
  const close = (restore = false) => {
    const previous = active;
    active?.setAttribute("aria-expanded", "false");
    active?.removeAttribute("aria-controls");
    active = undefined; menu.hidden = true;
    if (restore) previous?.focus();
  };
  const place = () => {
    if (!active?.isConnected) return close();
    const box = active.getBoundingClientRect(), edge = 8;
    const viewport = window.visualViewport;
    const left = viewport?.offsetLeft ?? 0, top = viewport?.offsetTop ?? 0;
    const width = viewport?.width ?? innerWidth, height = viewport?.height ?? innerHeight;
    if (!box.width || !box.height || box.bottom < top || box.top > top + height) return close();
    menu.style.maxWidth = `${width - 2 * edge}px`;
    menu.style.left = `${Math.max(left + edge, Math.min(box.left, left + width - menu.offsetWidth - edge))}px`;
    menu.style.top = `${box.bottom + edge + menu.offsetHeight <= top + height - edge
      ? box.bottom + edge : Math.max(top + edge, box.top - menu.offsetHeight - edge)}px`;
  };
  const open = (node, focus = false) => {
    close(); active = node;
    download.href = node.href; download.download = node.download;
    const destination = new URL("https://live.lean-lang.org/");
    destination.hash = new URLSearchParams({ project: "MathlibDemo", url: node.href }).toString();
    live.href = destination.href;
    node.setAttribute("aria-expanded", "true"); node.setAttribute("aria-controls", menu.id);
    menu.hidden = false; place();
    if (focus) download.focus();
  };
  document.addEventListener("click", event => {
    const node = event.target.closest?.("a[data-lean-declaration]");
    if (node && !event.ctrlKey && !event.metaKey && !event.shiftKey && !event.altKey) {
      event.preventDefault();
      if (active === node) close(); else open(node, event.detail === 0);
    } else if (!menu.contains(event.target)) close();
    else if (event.target.closest?.("a")) close();
  });
  document.addEventListener("keydown", event => {
    const node = event.target.closest?.("a[data-lean-declaration]");
    if (node && [" ", "ArrowDown", "ArrowUp"].includes(event.key)) {
      event.preventDefault(); open(node, true); if (event.key === "ArrowUp") live.focus();
    } else if (active && event.key === "Escape") { event.preventDefault(); close(true); }
    else if (menu.contains(event.target)) {
      if (["ArrowDown", "ArrowUp", "Home", "End"].includes(event.key)) {
        event.preventDefault();
        (event.key === "Home" ? download : event.key === "End" ? live : document.activeElement === download ? live : download).focus();
      } else if (event.key === "Tab") {
        // Continue from the source identifier in the document's tab order.
        close(true);
      }
    }
  });
  document.addEventListener("pointerdown", event => {
    if (active && !active.contains(event.target) && !menu.contains(event.target)) close();
  });
  document.addEventListener("focusin", event => {
    if (active && event.target !== active && !menu.contains(event.target)) close();
  });
  document.addEventListener("scroll", () => { if (active) place(); }, true);
  window.addEventListener("resize", () => { if (active) place(); });
  window.visualViewport?.addEventListener("resize", () => { if (active) place(); });
  window.visualViewport?.addEventListener("scroll", () => { if (active) place(); });
})();
