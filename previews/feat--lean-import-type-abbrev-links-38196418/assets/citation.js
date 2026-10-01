(() => {
  const RESET_DELAY = 2200;
  const TOUR_DELAY = 1200;

  function setupCitationTour() {
    const url = new URL(window.location.href);
    if (url.searchParams.get("tour") !== "citation") return;
    const target = document.getElementById("citation");
    if (!target) return;

    url.searchParams.delete("tour");
    window.history.replaceState(null, "", `${url.pathname}${url.search}${url.hash}`);

    const reveal = () => setTimeout(() => {
      const behavior = window.matchMedia("(prefers-reduced-motion: reduce)").matches ? "auto" : "smooth";
      target.setAttribute("tabindex", "-1");
      target.focus({ preventScroll: true });
      target.scrollIntoView({ behavior, block: "start" });
    }, TOUR_DELAY);

    if (document.readyState === "complete") reveal();
    else window.addEventListener("load", reveal, { once: true });
  }

  function legacyCopy(text) {
    const field = document.createElement("textarea");
    field.value = text;
    field.setAttribute("readonly", "");
    field.style.position = "fixed";
    field.style.opacity = "0";
    document.body.append(field);
    field.select();
    const copied = document.execCommand("copy");
    field.remove();
    if (!copied) throw new Error("copy command failed");
  }

  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      await navigator.clipboard.writeText(text);
      return;
    }
    legacyCopy(text);
  }

  setupCitationTour();

  for (const button of document.querySelectorAll("[data-copy-citation]")) {
    let resetTimer;
    button.addEventListener("click", async () => {
      const citation = document.getElementById(button.getAttribute("aria-controls"));
      const status = button.parentElement.querySelector(".citation-copy-status");
      if (!citation || !status) return;

      clearTimeout(resetTimer);
      try {
        await copyText(citation.textContent);
        button.classList.add("is-copied");
        button.setAttribute("aria-label", "BibTeX copied");
        button.title = "Copied";
        status.textContent = "Copied";
      } catch {
        button.classList.remove("is-copied");
        button.setAttribute("aria-label", "Could not copy BibTeX");
        button.title = "Could not copy";
        status.textContent = "Select and copy manually";
      }

      resetTimer = setTimeout(() => {
        button.classList.remove("is-copied");
        button.setAttribute("aria-label", "Copy BibTeX to clipboard");
        button.title = "Copy BibTeX";
        status.textContent = "";
      }, RESET_DELAY);
    });
  }
})();
