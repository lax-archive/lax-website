(() => {
  "use strict";

  const container = document.getElementById("remark42");
  if (!container) return;

  const host = (container.dataset.remark42Host || "").replace(/\/+$/, "");
  const siteId = container.dataset.remark42Site || "remark";
  const url = container.dataset.remark42Url || `${window.location.origin}${window.location.pathname}`;
  if (!host.startsWith("https://")) return;

  window.remark_config = {
    host,
    site_id: siteId,
    url,
    components: ["embed", "counter"],
    locale: "en",
    theme: "light",
    max_shown_comments: 50,
    show_email_subscription: false,
    show_rss_subscription: true,
    no_footer: false,
  };

  const unavailable = () => {
    const loading = container.querySelector(".discussion-loading");
    if (loading) loading.textContent = "Discussion is temporarily unavailable. Please try again later.";
  };

  for (const component of window.remark_config.components) {
    const script = document.createElement("script");
    let extension = ".js";
    if ("noModule" in script) {
      script.type = "module";
      extension = ".mjs";
    } else {
      script.async = true;
      script.defer = true;
    }
    script.src = `${host}/web/${component}${extension}`;
    script.addEventListener("error", unavailable, { once: true });
    (document.head || document.body).appendChild(script);
  }
})();
