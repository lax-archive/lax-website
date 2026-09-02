(() => {
  "use strict";

  const dialog = document.querySelector("[data-version-dialog]");
  const open = document.querySelector("[data-version-dialog-open]");
  const close = dialog?.querySelector("[data-version-dialog-close]");
  if (!dialog || !open) return;

  const closeDialog = () => {
    if (typeof dialog.close === "function") dialog.close();
    else dialog.removeAttribute("open");
  };

  open.addEventListener("click", () => {
    if (typeof dialog.showModal === "function") dialog.showModal();
    else dialog.setAttribute("open", "");
  });
  close?.addEventListener("click", closeDialog);
  dialog.addEventListener("click", (event) => {
    if (event.target === dialog) closeDialog();
  });
})();
