(() => {
  "use strict";

  const root = document.querySelector("[data-account-root]");
  const dialog = document.getElementById("account-dialog");
  if (!root || !dialog) return;

  const host = (root.dataset.remark42Host || "").replace(/\/+$/, "");
  const site = root.dataset.remark42Site || "remark";
  if (!host.startsWith("https://")) return;

  const authReturnParameter = "lax_auth_complete";
  const authPopupName = "lax-orcid-login";
  const authMessage = "lax-orcid-auth-complete";
  const conceptReviewCacheKey = "lax-concept-reviews:v1";
  const conceptReviewCacheTTL = 5 * 60 * 1000;
  const conceptReviewCacheLimit = 500;
  const authChannel = typeof window.BroadcastChannel === "function"
    ? new window.BroadcastChannel("lax-orcid-auth-v1")
    : null;

  const login = root.querySelector("[data-account-login]");
  const settings = root.querySelector("[data-account-settings]");
  const settingsLabel = settings?.querySelector("span:last-child");
  const close = dialog.querySelector("[data-account-close]");
  const content = dialog.querySelector("[data-account-content]");
  const status = dialog.querySelector("[data-account-status]");
  const nameLink = dialog.querySelector("[data-account-name]");
  const idLabel = dialog.querySelector("[data-account-id]");
  const avatar = dialog.querySelector("[data-account-avatar]");
  const refresh = dialog.querySelector("[data-account-refresh]");
  const logout = dialog.querySelector("[data-account-logout]");
  const commentList = dialog.querySelector("[data-account-comments]");
  const commentsStatus = dialog.querySelector("[data-account-comments-status]");
  const commentCount = dialog.querySelector("[data-account-comment-count]");
  const conceptReviewBadges = [...(document.querySelectorAll?.("[data-concept-review-url]") || [])];
  const conceptReviewProgresses = [...(document.querySelectorAll?.("[data-concept-review-progress]") || [])];
  const submissionConceptReview = document.querySelector("[data-submission-concept-urls]");
  const submissionFlaggedNote = document.querySelector("[data-submission-flagged-note]");
  const conceptReviewURLSet = new Set(conceptReviewBadges.map((badge) => badge.dataset.conceptReviewUrl).filter(Boolean));
  conceptReviewProgresses.forEach((progress) => readConceptReviewURLs(progress.dataset.conceptReviewUrls)
    .forEach((url) => conceptReviewURLSet.add(url)));
  readConceptReviewURLs(submissionConceptReview?.dataset.submissionConceptUrls)
    .forEach((url) => conceptReviewURLSet.add(url));
  const conceptReviewURLs = [...conceptReviewURLSet];
  let currentUser = null;
  let currentIdentity = null;
  let commentsLoadedFor = "";
  let conceptReviewState = new Map();
  let conceptReviewSequence = 0;
  let loginWatchTimer = null;
  let loginWatchUntil = 0;

  const bridgeOrigin = new URL(host).origin;
  const bridge = document.createElement("iframe");
  bridge.src = `${host}/reactions/v1/bridge`;
  bridge.title = "ORCID account session bridge";
  bridge.hidden = true;
  (document.body || document.head).appendChild(bridge);
  const bridgeRequests = new Map();
  let activeBridgeWindow = null;
  let bridgeSequence = 0;
  let markBridgeReady;
  const bridgeReady = new Promise((resolve) => { markBridgeReady = resolve; });

  window.addEventListener("message", (event) => {
    if (event.origin === window.location.origin && event.data?.source === authMessage) {
      finishLogin();
      return;
    }
    if (event.origin !== bridgeOrigin) return;
    const remarkFrame = document.querySelector("#remark42 iframe");
    const fromRemarkFrame = Boolean(remarkFrame?.contentWindow && event.source === remarkFrame.contentWindow);
    const fromFallbackBridge = Boolean(bridge.contentWindow && event.source === bridge.contentWindow);
    if (!fromRemarkFrame && !fromFallbackBridge) return;
    const message = event.data;
    if (!message || message.source !== "lax-reactions") return;
    if (message.type === "session-change") {
      if (fromRemarkFrame) activeBridgeWindow = remarkFrame.contentWindow;
      window.setTimeout(() => { void checkAccount(); }, 0);
      return;
    }
    if (message.type === "ready") {
      const switchedToRemarkFrame = fromRemarkFrame && activeBridgeWindow !== remarkFrame.contentWindow;
      if (fromRemarkFrame) activeBridgeWindow = remarkFrame.contentWindow;
      else if (!activeBridgeWindow) activeBridgeWindow = bridge.contentWindow;
      markBridgeReady();
      if (switchedToRemarkFrame) window.setTimeout(() => { void checkAccount(); }, 0);
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
      new Promise((_, reject) => window.setTimeout(() => reject(new Error("account bridge timed out")), 5000)),
    ]);
    const target = activeBridgeWindow || bridge.contentWindow;
    if (!target) throw new Error("account bridge is unavailable");
    const id = `lax-account-${Date.now()}-${bridgeSequence += 1}`;
    const response = new Promise((resolve, reject) => {
      const responseTimeout = action === "concepts" ? 12000 : 5000;
      const timeout = window.setTimeout(() => {
        bridgeRequests.delete(id);
        reject(new Error("account bridge timed out"));
      }, responseTimeout);
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

  const makeLoginUrl = (popup = false) => {
    const url = new URL("/auth/orcid/login", host);
    const returnUrl = new URL(window.location.href);
    // `host` was used only as a temporary preview cache buster. Never carry
    // it through OAuth, because back/forward caches can restore an old build.
    returnUrl.searchParams.delete("host");
    if (popup) returnUrl.searchParams.set(authReturnParameter, "1");
    else returnUrl.searchParams.delete(authReturnParameter);
    url.searchParams.set("from", returnUrl.toString());
    url.searchParams.set("site", site);
    return url.toString();
  };

  // Use a normal navigation for OAuth. The callback returns to a freshly
  // loaded archive page, so the header, reactions, and discussion all observe
  // the same new session without relying on a popup or cross-window timing.
  login.href = makeLoginUrl(false);
  refresh.href = makeLoginUrl(false);

  const stopLoginWatch = () => {
    loginWatchUntil = 0;
    if (loginWatchTimer !== null) {
      window.clearTimeout(loginWatchTimer);
      loginWatchTimer = null;
    }
  };

  const checkLoginWatch = async () => {
    loginWatchTimer = null;
    if (await checkAccount()) return;
    if (Date.now() >= loginWatchUntil) {
      stopLoginWatch();
      return;
    }
    loginWatchTimer = window.setTimeout(checkLoginWatch, 1500);
  };

  const startLoginWatch = (delay = 750) => {
    loginWatchUntil = Date.now() + (5 * 60 * 1000);
    if (loginWatchTimer !== null) window.clearTimeout(loginWatchTimer);
    loginWatchTimer = window.setTimeout(checkLoginWatch, delay);
  };

  const finishLogin = () => {
    startLoginWatch(0);
  };

  if (authChannel) authChannel.onmessage = (event) => {
    if (event.data?.source === authMessage) finishLogin();
  };

  const returnUrl = new URL(window.location.href);
  if (returnUrl.searchParams.get(authReturnParameter) === "1") {
    returnUrl.searchParams.delete(authReturnParameter);
    authChannel?.postMessage({ source: authMessage });
    if (window.opener && window.opener !== window) {
      window.opener.postMessage({ source: authMessage }, window.location.origin);
    }
    if (window.history?.replaceState) window.history.replaceState(null, "", returnUrl.toString());
    if (window.name === authPopupName) {
      window.close();
      return;
    }
  }

  window.addEventListener("LAX::login-request", (event) => {
    event.preventDefault();
    login.click();
  });
  const checkWhenForegrounded = () => {
    if (loginWatchUntil > Date.now()) startLoginWatch(0);
    else if (!currentUser) void checkAccount();
  };
  window.addEventListener("focus", checkWhenForegrounded);
  window.addEventListener("pageshow", checkWhenForegrounded);
  document.addEventListener?.("visibilitychange", () => {
    if (document.visibilityState === "visible") checkWhenForegrounded();
  });

  const validName = (value) => {
    const name = typeof value === "string" ? value.trim() : "";
    return name && !/^noname_/i.test(name) ? name : "";
  };

  const validOrcidId = (value) => {
    const id = typeof value === "string" ? value.trim().toUpperCase() : "";
    if (!/^\d{4}-\d{4}-\d{4}-\d{3}[\dX]$/.test(id)) return "";
    const chars = id.replaceAll("-", "");
    let total = 0;
    for (let i = 0; i < 15; i += 1) total = (total + Number(chars[i])) * 2;
    const result = (12 - (total % 11)) % 11;
    return chars[15] === (result === 10 ? "X" : String(result)) ? id : "";
  };

  async function directRequest(action, payload = {}) {
    if (action === "me") {
      const response = await fetch(`${host}/reactions/v1/me`, { credentials: "include", cache: "no-store", headers: { Accept: "application/json" } });
      return { ok: response.ok, status: response.status, data: await response.json() };
    }
    if (action === "comments") {
      const url = new URL(`${host}/api/v1/comments`);
      for (const [key, value] of Object.entries(payload)) url.searchParams.set(key, String(value));
      const response = await fetch(url, { credentials: "include", cache: "no-store", headers: { Accept: "application/json" } });
      return { ok: response.ok, status: response.status, data: await response.json() };
    }
    if (action === "concepts") {
      const response = await fetch(`${host}/reactions/v1/concepts`, {
        method: "POST",
        credentials: "include",
        cache: "no-store",
        headers: { Accept: "application/json", "Content-Type": "application/json" },
        body: JSON.stringify({ urls: payload.urls, viewer_orcid: payload.viewer_orcid }),
      });
      return { ok: response.ok, status: response.status, data: await response.json() };
    }
    const response = await fetch(`${host}/auth/logout`, { credentials: "include", cache: "no-store" });
    return { ok: response.ok, status: response.status, data: {} };
  }

  async function accountRequest(action, payload = {}) {
    try {
      return await bridgeRequest(action, payload);
    } catch {
      return directRequest(action, payload);
    }
  }

  function readConceptReviewURLs(value) {
    try {
      const urls = JSON.parse(value || "[]");
      return Array.isArray(urls) ? urls.filter((url) => typeof url === "string" && url) : [];
    } catch {
      return [];
    }
  }

  function validCachedConceptURL(value) {
    if (typeof value !== "string") return false;
    try {
      const parsed = new URL(value);
      return parsed.origin === "https://laxarchive.org" && parsed.pathname.endsWith(".html")
        && !parsed.search && !parsed.hash;
    } catch {
      return false;
    }
  }

  function readConceptReviewCache(viewerORCID) {
    const result = new Map();
    if (!viewerORCID) return result;
    try {
      const parsed = JSON.parse(window.localStorage?.getItem(conceptReviewCacheKey) || "null");
      if (parsed?.viewer_orcid !== viewerORCID || !Array.isArray(parsed.entries)) return result;
      const now = Date.now();
      for (const entry of parsed.entries) {
        const reaction = entry?.reaction === "endorse" || entry?.reaction === "flag" ? entry.reaction : "";
        const cachedAt = Number(entry?.cached_at);
        if (!validCachedConceptURL(entry?.url) || !Number.isFinite(cachedAt)
          || cachedAt > now || now - cachedAt > conceptReviewCacheTTL) continue;
        result.set(entry.url, { reaction, cachedAt });
      }
    } catch {
      // Storage can be disabled or contain data from an interrupted write.
    }
    return result;
  }

  function cacheConceptReviews(viewerORCID, reviews) {
    if (!viewerORCID || !Array.isArray(reviews)) return;
    try {
      const cached = readConceptReviewCache(viewerORCID);
      const now = Date.now();
      for (const review of reviews) {
        if (!validCachedConceptURL(review?.url)) continue;
        const reaction = review.viewer_reaction === "endorse" || review.viewer_reaction === "flag"
          ? review.viewer_reaction : "";
        cached.set(review.url, { reaction, cachedAt: now });
      }
      const entries = [...cached.entries()]
        .sort((left, right) => right[1].cachedAt - left[1].cachedAt)
        .slice(0, conceptReviewCacheLimit)
        .map(([url, entry]) => ({ url, reaction: entry.reaction, cached_at: entry.cachedAt }));
      window.localStorage?.setItem(conceptReviewCacheKey, JSON.stringify({ viewer_orcid: viewerORCID, entries }));
    } catch {
      // A cache failure must never prevent live review data from rendering.
    }
  }

  function renderConceptReviewBadge(badge, reaction, showPending = false) {
    const validReaction = reaction === "endorse" || reaction === "flag" ? reaction : "";
    const state = validReaction || (showPending ? "pending" : "");
    badge.hidden = !state;
    badge.className = `concept-review-badge${state ? ` ${state === "endorse" ? "endorsed" : state === "flag" ? "flagged" : "pending"}` : ""}`;
    badge.textContent = validReaction === "endorse" ? "✓" : validReaction === "flag" ? "⚑" : "";
    if (!state) {
      badge.title = "";
      badge.removeAttribute("role");
      badge.removeAttribute("aria-label");
      return;
    }
    const label = validReaction === "endorse"
      ? "You endorsed this concept"
      : validReaction === "flag" ? "You flagged this concept" : "You have not evaluated this concept";
    badge.title = label;
    badge.setAttribute("role", "img");
    badge.setAttribute("aria-label", label);
  }

  function renderConceptReviewLoading() {
    conceptReviewState = new Map();
    conceptReviewBadges.forEach((badge) => renderConceptReviewBadge(badge, ""));
    for (const progress of conceptReviewProgresses) {
      const track = progress.querySelector("[data-concept-review-progress-track]");
      const label = progress.querySelector("[data-concept-review-progress-label]");
      progress.hidden = false;
      progress.className = "concept-review-progress loading";
      if (label) label.textContent = "Loading review status...";
      track?.replaceChildren();
      track?.setAttribute("role", "progressbar");
      track?.setAttribute("aria-label", "Loading review status");
      track?.setAttribute("aria-busy", "true");
    }
    if (submissionFlaggedNote) submissionFlaggedNote.hidden = true;
  }

  function renderConceptReviewSummaries() {
    for (const progress of conceptReviewProgresses) {
      const urls = [...new Set(readConceptReviewURLs(progress.dataset.conceptReviewUrls))];
      const reactions = urls.map((url) => conceptReviewState.get(url) || "");
      const endorsed = reactions.filter((reaction) => reaction === "endorse").length;
      const flagged = reactions.filter((reaction) => reaction === "flag").length;
      const pending = reactions.length - endorsed - flagged;
      const evaluated = endorsed + flagged;
      const track = progress.querySelector("[data-concept-review-progress-track]");
      const label = progress.querySelector("[data-concept-review-progress-label]");
      progress.className = "concept-review-progress";
      progress.hidden = evaluated === 0;
      track?.setAttribute("role", "img");
      track?.removeAttribute("aria-busy");
      if (!track || !label || evaluated === 0 || reactions.length === 0) {
        track?.replaceChildren();
        if (label) label.textContent = "";
        track?.removeAttribute("aria-label");
        continue;
      }
      const endorsedPercentage = Math.round((endorsed / reactions.length) * 100);
      const flaggedPercentage = Math.round((flagged / reactions.length) * 100);
      const pendingPercentage = 100 - endorsedPercentage - flaggedPercentage;
      const description = `${endorsedPercentage}% accepted · ${pendingPercentage}% not evaluated · ${flaggedPercentage}% flagged`;
      label.textContent = description;
      track.setAttribute("aria-label", `Review progress: ${description}`);
      const orderedReactions = [
        ...reactions.filter((reaction) => reaction === "endorse"),
        ...reactions.filter((reaction) => reaction === ""),
        ...reactions.filter((reaction) => reaction === "flag"),
      ];
      track.replaceChildren(...orderedReactions.map((reaction) => {
        const segment = document.createElement("span");
        segment.className = `concept-review-progress-segment ${reaction === "endorse" ? "endorsed" : reaction === "flag" ? "flagged" : "pending"}`;
        segment.setAttribute("aria-hidden", "true");
        return segment;
      }));
    }

    if (!submissionFlaggedNote || !submissionConceptReview) return;
    const dependencies = [...new Set(readConceptReviewURLs(submissionConceptReview.dataset.submissionConceptUrls))];
    const flagged = dependencies.filter((url) => conceptReviewState.get(url) === "flag").length;
    submissionFlaggedNote.hidden = flagged === 0;
    const text = submissionFlaggedNote.querySelector("[data-submission-flagged-note-text]");
    if (text) text.textContent = flagged === 1
      ? "This submission contains or depends on a concept you flagged."
      : flagged > 1 ? `This submission contains or depends on ${flagged} concepts you flagged.` : "";
  }

  function renderLoadedConceptReviews(byURL) {
    conceptReviewState = byURL;
    const showReviewStates = [...byURL.values()].some((reaction) => reaction === "endorse" || reaction === "flag");
    conceptReviewBadges.forEach((badge) =>
      renderConceptReviewBadge(badge, byURL.get(badge.dataset.conceptReviewUrl), showReviewStates));
    renderConceptReviewSummaries();
  }

  function clearConceptReviewBadges() {
    conceptReviewSequence += 1;
    conceptReviewState = new Map();
    conceptReviewBadges.forEach((badge) => renderConceptReviewBadge(badge, ""));
    renderConceptReviewSummaries();
  }

  async function loadConceptReviewBadges() {
    if (!currentUser || !conceptReviewURLs.length) {
      clearConceptReviewBadges();
      return;
    }
    const sequence = conceptReviewSequence += 1;
    const viewerId = currentUser.id;
    const viewerORCID = currentIdentity?.orcidId || "";
    const urls = conceptReviewURLs;
    const cached = readConceptReviewCache(viewerORCID);
    const missingURLs = urls.filter((url) => !cached.has(url));
    if (missingURLs.length === 0) {
      renderLoadedConceptReviews(new Map(urls.map((url) => [url, cached.get(url).reaction])));
      return;
    }
    renderConceptReviewLoading();
    try {
      const reviews = [];
      for (let start = 0; start < missingURLs.length; start += 50) {
        const response = await accountRequest("concepts", {
          urls: missingURLs.slice(start, start + 50),
          viewer_orcid: viewerORCID,
        });
        if (!response.ok) throw new Error(String(response.status));
        if (Array.isArray(response.data?.concepts)) reviews.push(...response.data.concepts);
      }
      if (sequence !== conceptReviewSequence || currentUser?.id !== viewerId) return;
      const byURL = new Map(urls.map((url) => [url, cached.get(url)?.reaction || ""]));
      reviews.forEach((review) => {
        if (typeof review?.url !== "string" || !byURL.has(review.url)) return;
        byURL.set(review.url, review.viewer_reaction === "endorse" || review.viewer_reaction === "flag" ? review.viewer_reaction : "");
      });
      cacheConceptReviews(viewerORCID, reviews);
      renderLoadedConceptReviews(byURL);
    } catch {
      if (sequence !== conceptReviewSequence || currentUser?.id !== viewerId) return;
      conceptReviewState = new Map();
      conceptReviewBadges.forEach((badge) => renderConceptReviewBadge(badge, ""));
      renderConceptReviewSummaries();
    }
  }

  function initials(name) {
    const parts = name.split(/\s+/).filter(Boolean);
    return parts.slice(0, 2).map((part) => part[0]).join("").toUpperCase() || "iD";
  }

  function setLoggedOut(message = "") {
    currentUser = null;
    currentIdentity = null;
    commentsLoadedFor = "";
    clearConceptReviewBadges();
    login.hidden = false;
    settings.hidden = true;
    if (settingsLabel) settingsLabel.textContent = "Settings";
    content.hidden = true;
    status.hidden = false;
    status.textContent = message || "Sign in with ORCID to view your settings and comments.";
  }

  function accountEvent() {
    void loadConceptReviewBadges();
    window.dispatchEvent(new CustomEvent("LAX::account-ready", {
      detail: currentUser ? { authenticated: true, user: currentUser, identity: currentIdentity } : null,
    }));
  }

  window.addEventListener("LAX::review-change", (event) => {
    const changedURL = typeof event.detail?.url === "string" ? event.detail.url : "";
    if (!changedURL) return;
    const reaction = event.detail?.reaction === "endorse" || event.detail?.reaction === "flag" ? event.detail.reaction : "";
    cacheConceptReviews(currentIdentity?.orcidId || "", [{ url: changedURL, viewer_reaction: reaction }]);
    if (conceptReviewURLSet.has(changedURL)) {
      conceptReviewState.set(changedURL, reaction);
      const showReviewStates = Boolean(currentUser) && [...conceptReviewState.values()]
        .some((value) => value === "endorse" || value === "flag");
      conceptReviewBadges.forEach((badge) =>
        renderConceptReviewBadge(badge, conceptReviewState.get(badge.dataset.conceptReviewUrl), showReviewStates));
      renderConceptReviewSummaries();
    }
  });

  async function checkAccount() {
    try {
      const response = await accountRequest("me");
      if (!response.ok) throw new Error(String(response.status));
      if (!response.data?.authenticated || !response.data?.eligible) {
        const message = response.data?.reauthenticate
          ? "Your session expired. Sign in with ORCID again."
          : "Sign in with ORCID to view your settings and comments.";
        setLoggedOut(message);
        accountEvent();
        return false;
      }
      const viewer = response.data.viewer || {};
      const remarkId = typeof viewer.remark42_id === "string" ? viewer.remark42_id : "";
      const orcidId = validOrcidId(viewer.orcid_id);
      const displayName = validName(viewer.name);
      if (!/^orcid_[a-f0-9]{40}$/.test(remarkId) || !orcidId || !displayName) {
        setLoggedOut("A public name shared by ORCID is required before this account can comment or use settings.");
        accountEvent();
        return false;
      }
      currentUser = { id: remarkId, name: displayName };
      currentIdentity = { orcidId, name: displayName };
      login.hidden = true;
      settings.hidden = false;
      if (settingsLabel) settingsLabel.textContent = displayName;
      settings.title = `Account settings for ${displayName}`;
      content.hidden = false;
      status.hidden = true;
      nameLink.textContent = displayName;
      avatar.textContent = initials(displayName);
      nameLink.href = `https://orcid.org/${currentIdentity.orcidId}`;
      nameLink.title = `${displayName} — ORCID iD ${currentIdentity.orcidId}`;
      nameLink.setAttribute("aria-label", `${displayName}, ORCID iD ${currentIdentity.orcidId}`);
      nameLink.removeAttribute("aria-disabled");
      idLabel.textContent = `ORCID iD ${currentIdentity.orcidId}`;
      stopLoginWatch();
      accountEvent();
      return true;
    } catch {
      setLoggedOut();
      accountEvent();
      return false;
    }
  }

  function plainExcerpt(comment) {
    const raw = typeof comment.orig === "string" ? comment.orig : "";
    const fallback = typeof comment.text === "string" ? comment.text.replace(/<[^>]*>/g, " ") : "";
    const text = (raw || fallback).replace(/\s+/g, " ").trim();
    return text.length > 240 ? `${text.slice(0, 237).trimEnd()}…` : text;
  }

  function commentUrl(comment) {
    try {
      const url = new URL(comment.locator?.url || "");
      if (url.origin !== "https://laxarchive.org") return "";
      if (url.pathname.startsWith("/_reactions/")) return "";
      url.hash = `remark42__comment-${comment.id}`;
      return url.toString();
    } catch {
      return "";
    }
  }

  function renderComment(comment) {
    const item = document.createElement("li");
    item.className = "account-comment";
    const excerpt = document.createElement("p");
    excerpt.className = "account-comment-excerpt";
    excerpt.textContent = plainExcerpt(comment) || "Comment without text";
    const meta = document.createElement("p");
    meta.className = "account-comment-meta";
    const time = document.createElement("time");
    const date = new Date(comment.time);
    if (!Number.isNaN(date.valueOf())) {
      time.dateTime = date.toISOString();
      time.textContent = date.toLocaleDateString(undefined, { year: "numeric", month: "short", day: "numeric" });
      meta.appendChild(time);
    }
    const url = commentUrl(comment);
    if (url) {
      const link = document.createElement("a");
      link.href = url;
      link.textContent = comment.title ? `Open in ${comment.title}` : "Open comment";
      meta.appendChild(link);
    }
    item.append(excerpt, meta);
    return item;
  }

  async function loadComments() {
    if (!currentUser || commentsLoadedFor === currentUser.id) return;
    commentsLoadedFor = currentUser.id;
    commentList.replaceChildren();
    commentsStatus.textContent = "Loading your comments…";
    try {
      const all = [];
      const limit = 100;
      let skip = 0;
      let count = 0;
      do {
        const response = await accountRequest("comments", { site, user: currentUser.id, limit, skip });
        if (!response.ok) throw new Error(String(response.status));
        const page = response.data;
        const comments = Array.isArray(page.comments) ? page.comments : [];
        all.push(...comments);
        count = Number.isFinite(page.count) ? page.count : all.length;
        skip += comments.length;
        if (comments.length === 0) break;
      } while (skip < count);
      const visible = all.filter((comment) => commentUrl(comment));
      commentList.append(...visible.map(renderComment));
      commentCount.textContent = String(visible.length);
      commentsStatus.textContent = visible.length ? "" : "You have not posted any comments yet.";
    } catch {
      commentsLoadedFor = "";
      commentsStatus.textContent = "Your comments could not be loaded. Close settings and try again.";
    }
  }

  settings.addEventListener("click", () => {
    if (!currentUser) return;
    dialog.showModal();
    loadComments();
  });
  close.addEventListener("click", () => dialog.close());
  dialog.addEventListener("click", (event) => {
    if (event.target === dialog) dialog.close();
  });
  logout.addEventListener("click", async () => {
    logout.disabled = true;
    try {
      const response = await accountRequest("logout");
      if (!response.ok) {
        const session = await accountRequest("me");
        if (!session.ok || session.data?.authenticated) throw new Error(String(response.status));
      }
      dialog.close();
      setLoggedOut("You are signed out.");
      accountEvent();
    } catch {
      commentsStatus.textContent = "Sign out failed. Please try again.";
    } finally {
      logout.disabled = false;
    }
  });

  checkAccount();
})();
