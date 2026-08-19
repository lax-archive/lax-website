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
  let currentUser = null;
  let currentIdentity = null;
  let commentsLoadedFor = "";
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
      const timeout = window.setTimeout(() => {
        bridgeRequests.delete(id);
        reject(new Error("account bridge timed out"));
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

  function initials(name) {
    const parts = name.split(/\s+/).filter(Boolean);
    return parts.slice(0, 2).map((part) => part[0]).join("").toUpperCase() || "iD";
  }

  function setLoggedOut(message = "") {
    currentUser = null;
    currentIdentity = null;
    commentsLoadedFor = "";
    login.hidden = false;
    settings.hidden = true;
    if (settingsLabel) settingsLabel.textContent = "Settings";
    content.hidden = true;
    status.hidden = false;
    status.textContent = message || "Sign in with ORCID to view your settings and comments.";
  }

  function accountEvent() {
    window.dispatchEvent(new CustomEvent("LAX::account-ready", {
      detail: currentUser ? { user: currentUser, identity: currentIdentity } : null,
    }));
  }

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
      if (!response.ok) throw new Error(String(response.status));
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
