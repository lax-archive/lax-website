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
  const flagListOpen = reactions?.querySelector("[data-flag-list-open]");
  const flagListDialog = reactions?.querySelector("[data-flag-list-dialog]");
  const flagList = reactions?.querySelector("[data-flag-list]");
  const flagListEmpty = reactions?.querySelector("[data-flag-list-empty]");
  const flagEditor = reactions?.querySelector("[data-flag-editor]");
  const flagForm = reactions?.querySelector("[data-flag-form]");
  const flagMessage = reactions?.querySelector("[data-flag-message]");
  const flagLineStart = reactions?.querySelector("[data-flag-line-start]");
  const flagLineEnd = reactions?.querySelector("[data-flag-line-end]");
  const flagLinePicker = reactions?.querySelector("[data-flag-line-picker]");
  const flagLineSelection = reactions?.querySelector("[data-flag-line-selection]");
  const flagFormStatus = reactions?.querySelector("[data-flag-form-status]");
  const flagRemove = reactions?.querySelector("[data-flag-remove]");
  const reviewKind = reactions?.dataset?.reviewKind || "submission";
  const sourceLineCount = Number(reactions?.dataset?.sourceLines || 0);
  let reactionPending = false;
  let reactionData = null;
  let pickingFlagLines = false;
  let pickedFirstLine = 0;
  let linePickerInitialStart = "";
  let linePickerInitialEnd = "";
  let reactionLoadPromise = null;
  let lastReactionLoadAt = 0;
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
    if (message.type === "session-change") {
      if (fromRemarkFrame) activeBridgeWindow = remarkFrame.contentWindow;
      window.setTimeout(() => { void loadReactions(true); }, 0);
      return;
    }
    if (message.type === "ready") {
      const switchedToRemarkFrame = fromRemarkFrame && activeBridgeWindow !== remarkFrame.contentWindow;
      if (fromRemarkFrame) activeBridgeWindow = remarkFrame.contentWindow;
      else if (!activeBridgeWindow) activeBridgeWindow = bridge.contentWindow;
      markBridgeReady();
      if (switchedToRemarkFrame) window.setTimeout(() => { void loadReactions(true); }, 0);
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

  const renderVoters = (voters) => {
    const popover = reactions?.querySelector('[data-reaction-voters-popover="endorse"]');
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

  const closeDialog = (dialog) => {
    if (!dialog) return;
    if (typeof dialog.close === "function") dialog.close();
    else dialog.removeAttribute("open");
  };

  const openDialog = (dialog) => {
    if (!dialog || dialog.open === true) return;
    if (typeof dialog.showModal === "function") dialog.showModal();
    else dialog.setAttribute("open", "");
  };

  const normalizedFlags = (flags) => (Array.isArray(flags) ? flags : []).flatMap((flag) => {
    const orcid = validOrcidId(flag?.author?.orcid);
    const name = typeof flag?.author?.name === "string" ? flag.author.name.trim() : "";
    const message = typeof flag?.message === "string" ? flag.message.trim() : "";
    const id = typeof flag?.id === "string" && /^[A-Za-z0-9-]{1,128}$/.test(flag.id) ? flag.id : "";
    const start = Number.isInteger(flag?.line_start) ? flag.line_start : 0;
    const end = Number.isInteger(flag?.line_end) ? flag.line_end : 0;
    const hasRange = reviewKind === "concept" && start >= 1 && end >= start && end <= sourceLineCount && end - start < 500;
    if (!orcid || !name || !message || !id) return [];
    return [{ id, orcid, name, message, start: hasRange ? start : 0, end: hasRange ? end : 0, time: flag.time }];
  });

  const flagItemId = (id) => `review-flag-${id}`;

  const revealFlag = (id) => {
    openDialog(flagListDialog);
    window.setTimeout(() => {
      const item = document.getElementById(flagItemId(id));
      item?.scrollIntoView?.({ block: "nearest" });
      item?.classList.add("is-targeted");
      window.setTimeout(() => item?.classList.remove("is-targeted"), 1600);
    }, 0);
  };

  const renderSourceFlags = (flags) => {
    const railHost = document.querySelector("[data-source-review-rails]");
    if (!railHost) return;
    railHost.replaceChildren();
    document.querySelectorAll(".inline-contract-table tr.line-flagged, .inline-contract-table tr.line-pending-flag").forEach((row) => {
      row.classList.remove("line-flagged", "line-pending-flag");
    });
    const byStart = new Map();
    for (const flag of flags) {
      if (!flag.start) continue;
      for (let line = flag.start; line <= flag.end; line += 1) document.getElementById(`L${line}`)?.classList.add("line-flagged");
      const existing = byStart.get(flag.start) || [];
      existing.push(flag);
      byStart.set(flag.start, existing);
    }
    for (const [line, grouped] of byStart) {
      const rail = document.createElement("span");
      rail.className = "source-review-rail";
      rail.dataset.sourceLine = `L${line}`;
      const button = document.createElement("button");
      button.type = "button";
      button.className = "source-review-button";
      button.setAttribute("aria-label", `${grouped.length} flag${grouped.length === 1 ? "" : "s"} on source line ${line}`);
      button.title = grouped.length === 1 ? grouped[0].message : `${grouped.length} flags begin here`;
      button.textContent = grouped.length === 1 ? "🚩" : `🚩 ${grouped.length}`;
      button.addEventListener("click", () => revealFlag(grouped[0].id));
      rail.appendChild(button);
      railHost.appendChild(rail);
    }
    window.dispatchEvent(new CustomEvent("LAX::source-rails-changed"));
  };

  const renderFlags = (rawFlags) => {
    const flags = normalizedFlags(rawFlags);
    if (flagListEmpty) flagListEmpty.hidden = flags.length !== 0;
    if (flagList) flagList.replaceChildren(...flags.map((flag) => {
      const item = document.createElement("li");
      item.id = flagItemId(flag.id);
      item.className = "flag-list-item";
      const heading = document.createElement("div");
      heading.className = "flag-list-meta";
      const author = document.createElement("a");
      author.href = `https://orcid.org/${flag.orcid}`;
      author.target = "_blank";
      author.rel = "noopener noreferrer";
      author.textContent = flag.name;
      author.setAttribute("aria-label", `${flag.name}, ORCID iD ${flag.orcid}`);
      heading.appendChild(author);
      const date = new Date(flag.time);
      if (!Number.isNaN(date.valueOf())) {
        const time = document.createElement("time");
        time.dateTime = date.toISOString();
        time.textContent = date.toLocaleString();
        heading.appendChild(time);
      }
      const message = document.createElement("p");
      message.className = "flag-list-message";
      message.textContent = flag.message;
      item.append(heading, message);
      if (flag.start) {
        const range = document.createElement("button");
        range.type = "button";
        range.className = "flag-range-link";
        range.textContent = flag.start === flag.end ? `Go to line ${flag.start}` : `Go to lines ${flag.start}–${flag.end}`;
        range.addEventListener("click", () => {
          closeDialog(flagListDialog);
          const row = document.getElementById(`L${flag.start}`);
          row?.scrollIntoView?.({ behavior: "smooth", block: "center" });
          if (row) window.history?.replaceState?.(null, "", `#L${flag.start}`);
        });
        item.appendChild(range);
      }
      return item;
    }));
    renderSourceFlags(flags);
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
    renderVoters(data.voters?.endorse || []);
    renderFlags(data.flags);
    if (data.eligible) {
      setReactionStatus(`Signed in as ${data.viewer.name}`, "ready");
      if (reactionLogin) reactionLogin.hidden = true;
    } else if (data.authenticated) {
      setReactionStatus("Sign in again after making your ORCID name public.", "attention");
      if (reactionLogin) {
        reactionLogin.hidden = false;
      }
    } else {
      setReactionStatus("Sign in with ORCID to review.", "signed-out");
      if (reactionLogin) reactionLogin.hidden = false;
    }
  };

  const pendingReaction = () => {
    try {
      const reaction = window.sessionStorage.getItem(pendingReactionKey);
      return ["endorse", "flag"].includes(reaction) ? reaction : "";
    } catch {
      return "";
    }
  };

  const clearPendingReaction = () => {
    try { window.sessionStorage.removeItem(pendingReactionKey); } catch { /* storage can be disabled */ }
  };

  const saveReaction = async (reaction, details = {}) => {
    reactionPending = true;
    reactionButtons.forEach((item) => { item.disabled = true; });
    setReactionStatus("Saving your response…");
    try {
      const response = await reactionRequest("reaction", { url, reaction, ...details });
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

  const selectedLineRange = () => {
    const start = Number(flagLineStart?.value || 0);
    const end = Number(flagLineEnd?.value || 0);
    if (!start && !end) return { line_start: 0, line_end: 0 };
    if (!Number.isInteger(start) || !Number.isInteger(end) || start < 1 || end < start || end > sourceLineCount) return null;
    return { line_start: start, line_end: end };
  };

  const clearPendingRange = () => {
    document.querySelectorAll(".inline-contract-table tr.line-pending-flag").forEach((row) => row.classList.remove("line-pending-flag"));
  };

  const describeLineRange = (range) => {
    if (!flagLineSelection) return;
    if (!range || !range.line_start) {
      flagLineSelection.textContent = pickingFlagLines ? "Choose the first line in the source." : "No source lines selected.";
      return;
    }
    flagLineSelection.textContent = range.line_start === range.line_end
      ? `Line ${range.line_start} selected.`
      : `Lines ${range.line_start}–${range.line_end} selected.`;
  };

  const paintPendingRange = () => {
    clearPendingRange();
    const range = selectedLineRange();
    if (!range || !range.line_start) {
      describeLineRange(range);
      return;
    }
    for (let line = range.line_start; line <= range.line_end; line += 1) document.getElementById(`L${line}`)?.classList.add("line-pending-flag");
    describeLineRange(range);
  };

  const stopLinePicking = () => {
    pickingFlagLines = false;
    pickedFirstLine = 0;
    linePickerInitialStart = "";
    linePickerInitialEnd = "";
    document.documentElement?.classList?.remove("is-picking-flag-lines");
    if (flagLinePicker) flagLinePicker.textContent = "Select lines from source";
    clearPendingRange();
    describeLineRange(selectedLineRange());
    if (reactionData?.eligible) setReactionStatus(`Signed in as ${reactionData.viewer.name}`, "ready");
  };

  const cancelLinePicking = () => {
    if (flagLineStart) flagLineStart.value = linePickerInitialStart;
    if (flagLineEnd) flagLineEnd.value = linePickerInitialEnd;
    stopLinePicking();
  };

  const openFlagEditor = () => {
    const own = reactionData?.viewer_flag;
    if (flagMessage) flagMessage.value = typeof own?.message === "string" ? own.message : "";
    if (flagLineStart) flagLineStart.value = own?.line_start || "";
    if (flagLineEnd) flagLineEnd.value = own?.line_end || "";
    if (flagRemove) flagRemove.hidden = reactionData?.viewer_reaction !== "flag";
    if (flagFormStatus) flagFormStatus.textContent = "";
    stopLinePicking();
    openDialog(flagEditor);
    flagMessage?.focus?.();
  };

  const requestLogin = (pending) => {
    try { window.sessionStorage.setItem(pendingReactionKey, pending); } catch { /* storage can be disabled */ }
    let handled = false;
    if (typeof window.dispatchEvent === "function" && typeof CustomEvent === "function") {
      const request = new CustomEvent("LAX::login-request", { cancelable: true });
      handled = !window.dispatchEvent(request);
    }
    if (!handled) {
      if (typeof window.location.assign === "function") window.location.assign(reactionLoginURL.toString());
      else window.location.href = reactionLoginURL.toString();
    }
  };

  const loadReactions = (force = false) => {
    if (!reactions) return Promise.resolve();
    if (reactionLoadPromise) return reactionLoadPromise;
    if (!force && Date.now() - lastReactionLoadAt < 750) return Promise.resolve();
    reactionLoadPromise = (async () => {
      try {
        const response = await reactionRequest("page", { url });
        if (!response.ok) throw new Error(response.data?.error || `reaction service returned ${response.status}`);
        renderReactions(response.data);
        lastReactionLoadAt = Date.now();
        const queuedReaction = pendingReaction();
        if (queuedReaction && response.data.eligible) {
          clearPendingReaction();
          if (queuedReaction === "flag") openFlagEditor();
          else if (!await saveReaction(queuedReaction)) window.setTimeout(() => { void loadReactions(true); }, 0);
        }
      } catch {
        reactionButtons.forEach((button) => { button.disabled = true; });
        setReactionStatus("Page responses are temporarily unavailable.", "error");
      }
    })();
    return reactionLoadPromise.finally(() => { reactionLoadPromise = null; });
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
  flagListOpen?.addEventListener("click", () => openDialog(flagListDialog));
  reactions?.querySelector("[data-flag-list-close]")?.addEventListener("click", () => closeDialog(flagListDialog));
  reactions?.querySelectorAll("[data-flag-cancel]").forEach((button) => button.addEventListener("click", () => {
    stopLinePicking();
    closeDialog(flagEditor);
  }));
  flagEditor?.addEventListener("close", () => {
    // Selecting source lines intentionally closes the modal so the numbered
    // Lean source is reachable. Only an ordinary dialog dismissal cancels the
    // selection mode.
    if (!pickingFlagLines) stopLinePicking();
  });
  flagLinePicker?.addEventListener("click", () => {
    linePickerInitialStart = String(flagLineStart?.value || "");
    linePickerInitialEnd = String(flagLineEnd?.value || "");
    pickingFlagLines = true;
    pickedFirstLine = 0;
    document.documentElement?.classList?.add("is-picking-flag-lines");
    flagLinePicker.textContent = "Cancel line selection";
    closeDialog(flagEditor);
    setReactionStatus("Select the first and last source line for this flag. Press Escape to cancel.", "attention");
    document.querySelector(".inline-contract-table")?.scrollIntoView?.({ behavior: "smooth", block: "center" });
    if (flagLineSelection) flagLineSelection.textContent = "Choose the first line in the source.";
  });
  (document.querySelectorAll?.(".inline-contract-table .line-num a") || []).forEach((link) => link.addEventListener("click", (event) => {
    if (!pickingFlagLines) return;
    event.preventDefault();
    const line = Number(String(link.getAttribute("href") || "").replace("#L", ""));
    if (!Number.isInteger(line) || line < 1 || line > sourceLineCount) return;
    if (!pickedFirstLine) {
      pickedFirstLine = line;
      if (flagLineStart) flagLineStart.value = String(line);
      if (flagLineEnd) flagLineEnd.value = String(line);
      paintPendingRange();
      setReactionStatus(`Line ${line} selected; now choose the last line.`, "attention");
      if (flagLineSelection) flagLineSelection.textContent = `Line ${line} selected. Choose the last line.`;
      return;
    }
    const start = Math.min(pickedFirstLine, line);
    const end = Math.max(pickedFirstLine, line);
    if (flagLineStart) flagLineStart.value = String(start);
    if (flagLineEnd) flagLineEnd.value = String(end);
    stopLinePicking();
    openDialog(flagEditor);
  }));
  window.addEventListener("keydown", (event) => {
    if (!pickingFlagLines || event.key !== "Escape") return;
    event.preventDefault();
    cancelLinePicking();
    openDialog(flagEditor);
  });
  flagLineStart?.addEventListener("input", paintPendingRange);
  flagLineEnd?.addEventListener("input", paintPendingRange);
  flagForm?.addEventListener("submit", async (event) => {
    event.preventDefault();
    const message = String(flagMessage?.value || "").trim();
    const range = selectedLineRange();
    if (!message) {
      if (flagFormStatus) flagFormStatus.textContent = "Explain what appears incorrect before publishing the flag.";
      flagMessage?.focus?.();
      return;
    }
    if (!range) {
      if (flagFormStatus) flagFormStatus.textContent = "Choose both a valid start and end line, or leave both empty.";
      return;
    }
    if (flagFormStatus) flagFormStatus.textContent = "Publishing flag…";
    const saved = await saveReaction("flag", { message, ...range });
    if (!saved) {
      if (flagFormStatus) flagFormStatus.textContent = "The flag could not be published. Review the message and try again.";
      return;
    }
    stopLinePicking();
    closeDialog(flagEditor);
    if (reactionData?.viewer_flag?.id) revealFlag(reactionData.viewer_flag.id);
  });
  flagRemove?.addEventListener("click", async () => {
    if (flagFormStatus) flagFormStatus.textContent = "Removing flag…";
    if (!await saveReaction("clear")) {
      if (flagFormStatus) flagFormStatus.textContent = "The flag could not be removed. Try again.";
      return;
    }
    stopLinePicking();
    closeDialog(flagEditor);
  });
  for (const button of reactionButtons) {
    button.addEventListener("click", async () => {
      if (reactionPending || button.disabled) return;
      if (!reactionData?.eligible) {
        requestLogin(button.dataset.reaction);
        return;
      }
      const selected = button.dataset.reaction;
      if (selected === "flag") {
        openFlagEditor();
        return;
      }
      if (!await saveReaction(selected)) await loadReactions(true);
    });
  }
  window.addEventListener("LAX::account-ready", (event) => {
    const accountAuthenticated = Boolean(event?.detail?.authenticated);
    if (!reactionPending && accountAuthenticated !== Boolean(reactionData?.authenticated)) void loadReactions(true);
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
