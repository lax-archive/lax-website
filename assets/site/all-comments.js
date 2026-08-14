(() => {
  "use strict";

  const root = document.getElementById("all-comments");
  if (!root) return;
  const host = (root.dataset.remark42Host || "").replace(/\/+$/, "");
  const site = root.dataset.remark42Site || "remark";
  const identityUrl = root.dataset.identityUrl || "";
  const list = root.querySelector("[data-activity-list]");
  const status = root.querySelector("[data-activity-status]");
  const more = root.querySelector("[data-activity-more]");
  const pageSize = 20;
  const maximum = 1000;
  const identities = new Map();
  let comments = [];
  let shown = 0;

  const validOrcidId = (value) => {
    const id = typeof value === "string" ? value.trim().toUpperCase() : "";
    if (!/^\d{4}-\d{4}-\d{4}-\d{3}[\dX]$/.test(id)) return "";
    const chars = id.replaceAll("-", "");
    let total = 0;
    for (let i = 0; i < 15; i += 1) total = (total + Number(chars[i])) * 2;
    const result = (12 - (total % 11)) % 11;
    return chars[15] === (result === 10 ? "X" : String(result)) ? id : "";
  };

  const validName = (value) => {
    const name = typeof value === "string" ? value.trim() : "";
    return name && !/^noname_/i.test(name) ? name : "";
  };

  async function fetchJson(url) {
    const response = await fetch(url, { headers: { Accept: "application/json" }, cache: "no-store" });
    if (!response.ok) throw new Error(String(response.status));
    return response.json();
  }

  async function resolveIdentities(ids) {
    const missing = [...new Set(ids)].filter((id) => id && !identities.has(id));
    for (const id of missing) identities.set(id, null);
    if (!identityUrl) return;
    const batchBase = new URL(identityUrl);
    batchBase.pathname = batchBase.pathname.replace(/\/identity\/?$/, "/identities");
    for (let offset = 0; offset < missing.length; offset += 50) {
      const batch = missing.slice(offset, offset + 50);
      const url = new URL(batchBase);
      for (const id of batch) url.searchParams.append("remark42_id", id);
      try {
        const response = await fetchJson(url);
        for (const value of Array.isArray(response.identities) ? response.identities : []) {
          const orcidId = validOrcidId(value.orcid_id);
          const name = validName(value.name);
          if (orcidId && name && batch.includes(value.remark42_id)) {
            identities.set(value.remark42_id, { orcidId, name });
          }
        }
      } catch {
        // Keep missing mappings anonymous rather than showing stale stored names.
      }
    }
  }

  function excerpt(comment) {
    const raw = typeof comment.orig === "string" ? comment.orig : "";
    const fallback = typeof comment.text === "string" ? comment.text.replace(/<[^>]*>/g, " ") : "";
    const text = (raw || fallback).replace(/\s+/g, " ").trim();
    if (!text) return "Comment without text";
    return text.length > 280 ? `${text.slice(0, 277).trimEnd()}…` : text;
  }

  function sourceUrl(comment) {
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
    item.className = "activity-item";
    const header = document.createElement("div");
    header.className = "activity-item-header";
    const identity = identities.get(comment.user?.id);
    if (identity) {
      const author = document.createElement("a");
      author.className = "activity-author";
      author.href = `https://orcid.org/${identity.orcidId}`;
      author.target = "_blank";
      author.rel = "noreferrer";
      author.textContent = identity.name;
      header.appendChild(author);
    } else {
      const author = document.createElement("span");
      author.className = "activity-author activity-author-unavailable";
      author.textContent = "ORCID identity unavailable";
      header.appendChild(author);
    }
    const date = new Date(comment.time);
    if (!Number.isNaN(date.valueOf())) {
      const time = document.createElement("time");
      time.dateTime = date.toISOString();
      time.textContent = date.toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" });
      header.appendChild(time);
    }
    const body = document.createElement("p");
    body.className = "activity-excerpt";
    body.textContent = excerpt(comment);
    const footer = document.createElement("div");
    footer.className = "activity-item-footer";
    if (Number.isFinite(comment.score)) {
      const score = document.createElement("span");
      score.textContent = `Score ${comment.score}`;
      footer.appendChild(score);
    }
    const url = sourceUrl(comment);
    if (url) {
      const source = document.createElement("a");
      source.href = url;
      source.textContent = comment.title ? `Open ${comment.title}` : "Open source comment";
      footer.appendChild(source);
    }
    item.append(header, body, footer);
    return item;
  }

  async function showNext() {
    more.disabled = true;
    const next = comments.slice(shown, shown + pageSize);
    await resolveIdentities(next.map((comment) => comment.user?.id));
    list.append(...next.map(renderComment));
    shown += next.length;
    more.hidden = shown >= comments.length;
    more.disabled = false;
    if (shown < comments.length) {
      status.textContent = `Showing ${shown} of ${comments.length} newest comments.`;
    } else if (comments.length === maximum) {
      status.textContent = `Showing the ${maximum} newest comments, the maximum exposed by the activity API.`;
    } else {
      status.textContent = `Showing all ${comments.length} comments.`;
    }
  }

  async function load() {
    if (!host.startsWith("https://")) {
      status.textContent = "Comment activity is not configured.";
      root.setAttribute("aria-busy", "false");
      return;
    }
    try {
      const url = new URL(`${host}/api/v1/last/${maximum}`);
      url.searchParams.set("site", site);
      const response = await fetchJson(url);
      comments = (Array.isArray(response) ? response : [])
        .filter((comment) => comment && !comment.delete && sourceUrl(comment))
        .sort((a, b) => new Date(b.time).valueOf() - new Date(a.time).valueOf());
      if (!comments.length) {
        status.textContent = "No public comments have been posted yet.";
      } else {
        await showNext();
      }
    } catch {
      status.textContent = "Comments could not be loaded. Please try again later.";
    } finally {
      root.setAttribute("aria-busy", "false");
    }
  }

  more.addEventListener("click", showNext);
  load();
})();
