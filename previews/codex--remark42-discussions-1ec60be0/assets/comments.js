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
  const reactionButtons = reactions ? [...reactions.querySelectorAll("[data-reaction]")] : [];
  const reactionVoterToggles = reactions ? [...reactions.querySelectorAll("[data-reaction-voters]")] : [];
  const reactionLogin = reactions?.querySelector("[data-reactions-login]");
  let reactionPending = false;
  let reactionData = null;
  const pendingReactionKey = `lax-reaction-pending:${url}`;

  const reactionLoginURL = new URL(`${host}/auth/orcid/login`);
  reactionLoginURL.searchParams.set("site", siteId);
  reactionLoginURL.searchParams.set("from", window.location.href);

  const bridgeOrigin = new URL(host).origin;
  const bridge = document.createElement("iframe");
  bridge.src = `${host}/reactions/v1/bridge`;
  bridge.title = "Reaction session bridge";
  bridge.hidden = true;
  (document.body || document.head).appendChild(bridge);
  const bridgeRequests = new Map();
  let activeBridgeWindow = null;
  let bridgeSequence = 0;
  let markBridgeReady;
  const bridgeReady = new Promise((resolve) => { markBridgeReady = resolve; });

  window.addEventListener("message", (event) => {
    if (event.origin !== bridgeOrigin) return;
    const remarkFrame = document.querySelector("#remark42 iframe");
    const fromRemarkFrame = Boolean(remarkFrame?.contentWindow && event.source === remarkFrame.contentWindow);
    const fromFallbackBridge = Boolean(bridge.contentWindow && event.source === bridge.contentWindow);
    if (!fromRemarkFrame && !fromFallbackBridge) return;
    const message = event.data;
    if (!message || message.source !== "lax-reactions") return;
    if (message.type === "ready") {
      if (fromRemarkFrame || !activeBridgeWindow) activeBridgeWindow = event.source;
      markBridgeReady();
      if (fromRemarkFrame) window.setTimeout(() => { void loadReactions(); }, 0);
      return;
    }
    const pending = typeof message.id === "string" ? bridgeRequests.get(message.id) : null;
    if (!pending || pending.source !== event.source) return;
    bridgeRequests.delete(message.id);
    pending.resolve(message);
  });

  async function bridgeRequest(action, payload = {}) {
    await Promise.race([
      bridgeReady,
      new Promise((_, reject) => window.setTimeout(() => reject(new Error("reaction bridge timed out")), 5000)),
    ]);
    const target = activeBridgeWindow || bridge.contentWindow;
    if (!target) throw new Error("reaction bridge is unavailable");
    const id = `lax-${Date.now()}-${bridgeSequence += 1}`;
    const response = new Promise((resolve, reject) => {
      const timeout = window.setTimeout(() => {
        bridgeRequests.delete(id);
        reject(new Error("reaction bridge timed out"));
      }, 5000);
      bridgeRequests.set(id, {
        source: target,
        resolve: (message) => {
          window.clearTimeout(timeout);
          resolve(message);
        },
      });
    });
    target.postMessage({ source: "lax-reactions", id, action, ...payload }, bridgeOrigin);
    return response;
  }

  async function directRequest(action, payload = {}) {
    if (action === "page") {
      const response = await window.fetch(`${host}/reactions/v1/page?url=${encodeURIComponent(payload.url)}`, {
        credentials: "include",
        headers: { Accept: "application/json" },
      });
      return { ok: response.ok, status: response.status, data: await response.json() };
    }
    const response = await window.fetch(`${host}/reactions/v1/reaction`, {
      method: "PUT",
      credentials: "include",
      headers: { "Content-Type": "application/json", "X-Lax-CSRF": "1", Accept: "application/json" },
      body: JSON.stringify(payload),
    });
    return { ok: response.ok, status: response.status, data: await response.json() };
  }

  async function reactionRequest(action, payload) {
    try {
      return await bridgeRequest(action, payload);
    } catch {
      // Older deployments do not expose the same-origin bridge. The direct
      // request remains a compatibility path for browsers without partitioning.
      return directRequest(action, payload);
    }
  }

  const validOrcidId = (value) => {
    const id = typeof value === "string" ? value.trim().toUpperCase() : "";
    if (!/^\d{4}-\d{4}-\d{4}-\d{3}[\dX]$/.test(id)) return "";
    const chars = id.replaceAll("-", "");
    let total = 0;
    for (let i = 0; i < 15; i += 1) total = (total + Number(chars[i])) * 2;
    const result = (12 - (total % 11)) % 11;
    return chars[15] === (result === 10 ? "X" : String(result)) ? id : "";
  };

  const setReactionStatus = (message, kind = "") => {
    if (!reactionStatus) return;
    reactionStatus.textContent = message;
    reactionStatus.dataset.state = kind;
  };

  const renderVoters = (reaction, voters) => {
    const popover = reactions?.querySelector(`[data-reaction-voters-popover="${reaction}"]`);
    const list = popover?.querySelector("ul");
    const empty = popover?.querySelector("[data-reaction-empty]");
    if (!popover || !list) return;
    const identities = voters.flatMap((voter) => {
      const orcid = validOrcidId(voter.orcid);
      const name = typeof voter.name === "string" ? voter.name.trim() : "";
      return orcid && name ? [{ orcid, name }] : [];
    });
    list.replaceChildren(...identities.map((voter) => {
      const item = document.createElement("li");
      const link = document.createElement("a");
      link.href = `https://orcid.org/${voter.orcid}`;
      link.target = "_blank";
      link.rel = "noopener noreferrer";
      link.textContent = voter.name;
      link.title = `${voter.name} — ORCID iD ${voter.orcid}`;
      link.setAttribute("aria-label", `${voter.name}, ORCID iD ${voter.orcid}`);
      item.appendChild(link);
      return item;
    }));
    if (empty) empty.hidden = identities.length !== 0;
  };

  const renderReactions = (data) => {
    reactionData = data;
    for (const button of reactionButtons) {
      const reaction = button.dataset.reaction;
      const active = data.viewer_reaction === reaction;
      button.disabled = reactionPending;
      button.setAttribute("aria-pressed", String(active));
      const counter = reactions?.querySelector(`[data-reaction-count="${reaction}"]`);
      if (counter) counter.textContent = String(data.counts?.[reaction] || 0);
    }
    renderVoters("like", data.voters?.like || []);
    renderVoters("dislike", data.voters?.dislike || []);
    renderVoters("rocket", data.voters?.rocket || []);
    if (data.eligible) {
      setReactionStatus(`Signed in as ${data.viewer.name}`, "ready");
      if (reactionLogin) reactionLogin.hidden = true;
    } else if (data.authenticated) {
      setReactionStatus("Sign in again after making your ORCID name public.", "attention");
      if (reactionLogin) {
        reactionLogin.hidden = false;
      }
    } else {
      setReactionStatus("Sign in with ORCID to react.", "signed-out");
      if (reactionLogin) reactionLogin.hidden = false;
    }
  };

  const pendingReaction = () => {
    try {
      const reaction = window.sessionStorage.getItem(pendingReactionKey);
      return ["like", "dislike", "rocket"].includes(reaction) ? reaction : "";
    } catch {
      return "";
    }
  };

  const clearPendingReaction = () => {
    try { window.sessionStorage.removeItem(pendingReactionKey); } catch { /* storage can be disabled */ }
  };

  const saveReaction = async (reaction) => {
    reactionPending = true;
    reactionButtons.forEach((item) => { item.disabled = true; });
    setReactionStatus("Saving your response…");
    try {
      const response = await reactionRequest("reaction", { url, reaction });
      const data = response.data;
      if (!response.ok) throw new Error(data?.error || `reaction service returned ${response.status}`);
      reactionPending = false;
      renderReactions(data);
      return true;
    } catch (error) {
      reactionPending = false;
      setReactionStatus(error instanceof Error ? error.message : "Unable to save your response.", "error");
      return false;
    }
  };

  const loadReactions = async () => {
    if (!reactions) return;
    try {
      const response = await reactionRequest("page", { url });
      if (!response.ok) throw new Error(response.data?.error || `reaction service returned ${response.status}`);
      renderReactions(response.data);
      const queuedReaction = pendingReaction();
      if (queuedReaction && response.data.eligible) {
        clearPendingReaction();
        if (!await saveReaction(queuedReaction)) await loadReactions();
      }
    } catch {
      reactionButtons.forEach((button) => { button.disabled = true; });
      setReactionStatus("Page responses are temporarily unavailable.", "error");
    }
  };

  if (reactionLogin) {
    reactionLogin.href = reactionLoginURL.toString();
  }
  for (const toggle of reactionVoterToggles) {
    toggle.addEventListener("click", () => {
      const reaction = toggle.dataset.reactionVoters;
      const popover = reactions?.querySelector(`[data-reaction-voters-popover="${reaction}"]`);
      if (!popover) return;
      const willOpen = popover.hidden;
      for (const other of reactionVoterToggles) {
        const otherPopover = reactions?.querySelector(`[data-reaction-voters-popover="${other.dataset.reactionVoters}"]`);
        if (otherPopover) otherPopover.hidden = true;
        other.setAttribute("aria-expanded", "false");
      }
      popover.hidden = !willOpen;
      toggle.setAttribute("aria-expanded", String(willOpen));
    });
  }
  for (const button of reactionButtons) {
    button.addEventListener("click", async () => {
      if (reactionPending || button.disabled) return;
      if (!reactionData?.eligible) {
        try { window.sessionStorage.setItem(pendingReactionKey, button.dataset.reaction); } catch { /* storage can be disabled */ }
        let handled = false;
        if (typeof window.dispatchEvent === "function" && typeof CustomEvent === "function") {
          const request = new CustomEvent("LAX::login-request", { cancelable: true });
          handled = !window.dispatchEvent(request);
        }
        if (!handled) {
          if (typeof window.location.assign === "function") window.location.assign(reactionLoginURL.toString());
          else window.location.href = reactionLoginURL.toString();
        }
        return;
      }
      const selected = button.dataset.reaction;
      if (!await saveReaction(selected)) await loadReactions();
    });
  }
  window.addEventListener("LAX::account-ready", (event) => {
    if (event.detail?.user && !reactionPending) void loadReactions();
  });
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
    // Remark passes unknown config keys through to the iframe URL. This keeps
    // browsers from reusing the pre-ORCID author UI after the server upgrade.
    lax_ui: "orcid-v2",
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
