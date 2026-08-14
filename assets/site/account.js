(() => {
  "use strict";

  const root = document.querySelector("[data-account-root]");
  const dialog = document.getElementById("account-dialog");
  if (!root || !dialog) return;

  const host = (root.dataset.remark42Host || "").replace(/\/+$/, "");
  const site = root.dataset.remark42Site || "remark";
  const identityUrl = root.dataset.identityUrl || "";
  if (!host.startsWith("https://")) return;

  const login = root.querySelector("[data-account-login]");
  const settings = root.querySelector("[data-account-settings]");
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

  const makeLoginUrl = () => {
    const url = new URL("/auth/orcid/login", host);
    url.searchParams.set("from", window.location.href);
    url.searchParams.set("site", site);
    return url.toString();
  };

  login.href = makeLoginUrl();
  refresh.href = makeLoginUrl();

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

  async function fetchJson(url, options = {}) {
    const response = await fetch(url, {
      credentials: "include",
      cache: "no-store",
      headers: { Accept: "application/json" },
      ...options,
    });
    if (!response.ok) throw new Error(String(response.status));
    return response.json();
  }

  async function findIdentity(user) {
    if (!identityUrl || !user?.id) return null;
    const url = new URL(identityUrl);
    url.searchParams.set("remark42_id", user.id);
    try {
      const value = await fetchJson(url);
      const orcidId = validOrcidId(value.orcid_id);
      const name = validName(value.name);
      if (!orcidId || !name || (value.remark42_id && value.remark42_id !== user.id)) return null;
      return { orcidId, name };
    } catch {
      return null;
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
      const user = await fetchJson(`${host}/api/v1/user?site=${encodeURIComponent(site)}`);
      const sessionName = validName(user.name);
      if (!sessionName) {
        setLoggedOut("A public name shared by ORCID is required before this account can comment or use settings.");
        accountEvent();
        return;
      }
      currentUser = user;
      currentIdentity = await findIdentity(user);
      const displayName = currentIdentity?.name || sessionName;
      login.hidden = true;
      settings.hidden = false;
      settings.title = `Account settings for ${displayName}`;
      content.hidden = false;
      status.hidden = true;
      nameLink.textContent = displayName;
      avatar.textContent = initials(displayName);
      if (currentIdentity) {
        nameLink.href = `https://orcid.org/${currentIdentity.orcidId}`;
        nameLink.removeAttribute("aria-disabled");
        idLabel.textContent = `ORCID iD ${currentIdentity.orcidId}`;
      } else {
        nameLink.removeAttribute("href");
        nameLink.setAttribute("aria-disabled", "true");
        idLabel.textContent = "The public ORCID profile link is temporarily unavailable.";
      }
      accountEvent();
    } catch {
      setLoggedOut();
      accountEvent();
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
        const url = new URL(`${host}/api/v1/comments`);
        url.searchParams.set("site", site);
        url.searchParams.set("user", currentUser.id);
        url.searchParams.set("limit", String(limit));
        url.searchParams.set("skip", String(skip));
        const page = await fetchJson(url);
        const comments = Array.isArray(page.comments) ? page.comments : [];
        all.push(...comments);
        count = Number.isFinite(page.count) ? page.count : all.length;
        skip += comments.length;
        if (comments.length === 0) break;
      } while (skip < count);
      commentList.append(...all.map(renderComment));
      commentCount.textContent = String(count);
      commentsStatus.textContent = count ? "" : "You have not posted any comments yet.";
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
      await fetch(`${host}/auth/logout`, { credentials: "include", cache: "no-store" });
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
