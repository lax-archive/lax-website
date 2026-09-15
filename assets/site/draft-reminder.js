(() => {
  "use strict";

  const dialog = document.querySelector("[data-draft-reminder]");
  if (!dialog) return;

  const createdAt = Date.parse(dialog.dataset.createdAt || "");
  const sevenDays = 7 * 24 * 60 * 60 * 1000;
  if (!Number.isFinite(createdAt) || Date.now() - createdAt < sevenDays) return;

  const storageKey = `lax:draft-reminder:${dialog.dataset.submissionId || "unknown"}`;
  try {
    if (window.sessionStorage.getItem(storageKey)) return;
    window.sessionStorage.setItem(storageKey, "shown");
  } catch {
    // Storage can be disabled. The reminder should still be shown.
  }

  const close = dialog.querySelector("[data-draft-reminder-close]");
  const closeDialog = () => {
    if (typeof dialog.close === "function") dialog.close();
    else dialog.removeAttribute("open");
  };

  close?.addEventListener("click", closeDialog);
  dialog.addEventListener("click", (event) => {
    if (event.target === dialog) closeDialog();
  });

  if (typeof dialog.showModal === "function") dialog.showModal();
  else dialog.setAttribute("open", "");
})();
