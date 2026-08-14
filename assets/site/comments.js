(() => {
  "use strict";

  const container = document.getElementById("remark42");
  if (!container) return;
  const status = document.getElementById("remark42-status");

  const host = (container.dataset.remark42Host || "").replace(/\/+$/, "");
  const siteId = container.dataset.remark42Site || "remark";
  const url = container.dataset.remark42Url || `${window.location.origin}${window.location.pathname}`;
  if (!host.startsWith("https://")) return;

  const reactions = document.querySelector("[data-reactions-host]");
  const reactionStatus = reactions?.querySelector("[data-reactions-status]");
  const reactionButtons = reactions ? [...reactions.querySelectorAll("[data-reaction-vote]")] : [];
  const reactionLogin = reactions?.querySelector("[data-reactions-login]");
  let reactionPending = false;

  const setReactionStatus = (message, kind = "") => {
    if (!reactionStatus) return;
    reactionStatus.textContent = message;
    reactionStatus.dataset.state = kind;
  };

  const renderVoters = (vote, voters) => {
    const details = reactions?.querySelector(`[data-reaction-voters="${vote}"]`);
    const list = details?.querySelector("ul");
    if (!details || !list) return;
    list.replaceChildren(...voters.map((voter) => {
      const item = document.createElement("li");
      const link = document.createElement("a");
      link.href = `https://orcid.org/${encodeURIComponent(voter.orcid)}`;
      link.target = "_blank";
      link.rel = "noopener noreferrer";
      link.textContent = voter.name;
      item.appendChild(link);
      return item;
    }));
    details.hidden = voters.length === 0;
  };

  const renderReactions = (data) => {
    for (const button of reactionButtons) {
      const vote = Number(button.dataset.reactionVote);
      const active = data.viewer_vote === vote;
      button.disabled = reactionPending || !data.eligible;
      button.setAttribute("aria-pressed", String(active));
      button.querySelector("[data-reaction-count]").textContent = String(vote === 1 ? data.likes : data.dislikes);
    }
    renderVoters("1", data.voters.likes);
    renderVoters("-1", data.voters.dislikes);
    if (data.eligible) {
      setReactionStatus(`Signed in as ${data.viewer.name}`, "ready");
      if (reactionLogin) reactionLogin.hidden = true;
    } else if (data.authenticated) {
      setReactionStatus("Sign in again after making your ORCID name public.", "attention");
      if (reactionLogin) {
        reactionLogin.hidden = false;
        reactionLogin.textContent = "Sign in again";
      }
    } else {
      setReactionStatus("Sign in with ORCID to vote.", "signed-out");
      if (reactionLogin) reactionLogin.hidden = false;
    }
  };

  const reactionsURL = `${host}/reactions/v1/page?url=${encodeURIComponent(url)}`;
  const loadReactions = async () => {
    if (!reactions) return;
    try {
      const response = await window.fetch(reactionsURL, { credentials: "include", headers: { Accept: "application/json" } });
      if (!response.ok) throw new Error(`reaction service returned ${response.status}`);
      renderReactions(await response.json());
    } catch {
      reactionButtons.forEach((button) => { button.disabled = true; });
      setReactionStatus("Page responses are temporarily unavailable.", "error");
    }
  };

  if (reactionLogin) {
    const loginURL = new URL(`${host}/auth/orcid/login`);
    loginURL.searchParams.set("site", siteId);
    loginURL.searchParams.set("from", window.location.href);
    reactionLogin.href = loginURL.toString();
  }
  for (const button of reactionButtons) {
    button.addEventListener("click", async () => {
      if (reactionPending || button.disabled) return;
      const selected = Number(button.dataset.reactionVote);
      const vote = button.getAttribute("aria-pressed") === "true" ? 0 : selected;
      reactionPending = true;
      reactionButtons.forEach((item) => { item.disabled = true; });
      setReactionStatus("Saving your response…");
      try {
        const response = await window.fetch(`${host}/reactions/v1/vote`, {
          method: "PUT",
          credentials: "include",
          headers: { "Content-Type": "application/json", "X-Lax-CSRF": "1", Accept: "application/json" },
          body: JSON.stringify({ url, vote }),
        });
        const data = await response.json();
        if (!response.ok) throw new Error(data.error || `reaction service returned ${response.status}`);
        reactionPending = false;
        renderReactions(data);
      } catch (error) {
        reactionPending = false;
        setReactionStatus(error instanceof Error ? error.message : "Unable to save your response.", "error");
        await loadReactions();
      }
    });
  }
  void loadReactions();

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
    if (status) status.textContent = "Discussion is temporarily unavailable. Please try again later.";
  };

  window.addEventListener("REMARK42::ready", () => status?.remove(), { once: true });

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
