(() => {
  "use strict";

  const dialog = document.querySelector("[data-draft-reminder]");
  if (!dialog) return;

  const createdAt = Date.parse(dialog.dataset.createdAt || "");
  const fourteenDays = 14 * 24 * 60 * 60 * 1000;
  if (!Number.isFinite(createdAt) || Date.now() - createdAt < fourteenDays) return;

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
