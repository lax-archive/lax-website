// The page shell and small html helpers, following the reference design:
// sticky header (hamburger + centered title), collapsible sidebar with
// search/filters, and a single content pane. Only sidebar.js, layout.js and
// dag.js run in the browser; everything else is rendered at build time.

import { siteAssetVersion } from "./assets.js";
import {
  DEFAULT_SITE_URL,
  REMARK42_IDENTITY_URL,
  REMARK42_SITE_ID,
  REMARK42_URL,
} from "../config.js";

const HONESTY_TOOLTIP =
  "Proven by the pipeline's least fixed point; until proof security v0.3, this also rests on submitter honesty.";

export function esc(value: string): string {
  return value.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

export function attr(value: string): string { return esc(value); }

export interface PageShell {
  /** the <title> */
  title: string;
  /** relative prefix to the site root: "" or "../" */
  rootRel: string;
  /** inner html of the <aside id="sidebar"> */
  sidebar: string;
  /** inner html of the content pane */
  content: string;
  /** additional scripts (site-relative paths) loaded after sidebar.js */
  scripts?: string[];
}

const REMARK42_ORIGIN = new URL(REMARK42_URL).origin;
const ACCOUNT_CONNECT_ORIGINS = [...new Set([
  REMARK42_ORIGIN,
  new URL(REMARK42_IDENTITY_URL).origin,
])].join(" ");
const BASE_CSP =
  `default-src 'none'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src https: data:; font-src 'self'; connect-src ${ACCOUNT_CONNECT_ORIGINS}`;

function contentSecurityPolicy(hasDiscussion: boolean): string {
  if (!hasDiscussion) return BASE_CSP;
  return `default-src 'none'; script-src 'self' ${REMARK42_ORIGIN}; style-src 'self' 'unsafe-inline'; img-src https: data:; font-src 'self'; frame-src ${REMARK42_ORIGIN}; connect-src ${ACCOUNT_CONNECT_ORIGINS}`;
}

function accountLoginHref(): string {
  const url = new URL("/auth/orcid/login", REMARK42_URL);
  url.searchParams.set("from", DEFAULT_SITE_URL);
  url.searchParams.set("site", REMARK42_SITE_ID);
  return url.toString();
}

function accountUi(): string {
  return `<div class="account-header" data-account-root data-remark42-host="${attr(REMARK42_URL)}" data-remark42-site="${attr(REMARK42_SITE_ID)}" data-identity-url="${attr(REMARK42_IDENTITY_URL)}">
  <a class="account-control" data-account-login href="${attr(accountLoginHref())}"><span class="orcid-mark" aria-hidden="true">iD</span><span>Sign in with ORCID</span></a>
  <button class="account-control" data-account-settings type="button" aria-haspopup="dialog" aria-controls="account-dialog" hidden><span class="orcid-mark" aria-hidden="true">iD</span><span>Settings</span></button>
</div>`;
}

function accountDialog(): string {
  return `<dialog class="account-dialog" id="account-dialog" aria-labelledby="account-dialog-title">
<div class="account-dialog-inner">
<header class="account-dialog-header">
<div><p class="account-dialog-eyebrow">ORCID account</p><h2 id="account-dialog-title">Settings</h2></div>
<button class="account-dialog-close" data-account-close type="button" aria-label="Close account settings">×</button>
</header>
<div class="account-dialog-body">
<p class="account-status" data-account-status role="status">Checking your ORCID session…</p>
<section data-account-content hidden>
<div class="account-identity">
<span class="account-avatar" data-account-avatar aria-hidden="true">iD</span>
<div><a class="account-name" data-account-name target="_blank" rel="noopener noreferrer"></a><p class="account-id" data-account-id></p></div>
</div>
<p class="account-name-note">Your public name comes from ORCID. ORCID names are self-asserted and may change.</p>
<div class="account-actions">
<a data-account-refresh href="${attr(accountLoginHref())}">Refresh from ORCID</a>
<button data-account-logout type="button">Sign out</button>
</div>
<div class="account-comments-heading"><h3>Your comments</h3><span data-account-comment-count></span></div>
<ol class="account-comments" data-account-comments></ol>
<p class="account-comments-status" data-account-comments-status role="status"></p>
</section>
</div>
</div>
</dialog>`;
}

// Inline data: URI so the icon loads under the CSP everywhere — including
// plain-http `lax serve`, where an assets/ file would violate `img-src`.
const FAVICON = "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Crect width='64' height='64' rx='12' fill='%232a7f8f'/%3E%3Cpath d='M18 14v36h29v-8H27V14z' fill='%23fff'/%3E%3C/svg%3E";

export function page(shell: PageShell): string {
  const root = shell.rootRel;
  const csp = contentSecurityPolicy(shell.scripts?.includes("assets/comments.js") ?? false);
  const scripts = ["assets/sidebar.js", "assets/account.js", ...(shell.scripts ?? [])]
    .map((src) => `<script src="${attr(root + src)}?v=${siteAssetVersion(src.replace(/^assets\//, ""))}"></script>`)
    .join("\n");
  const stylesheet = (src: string) => `${root}assets/${src}?v=${siteAssetVersion(src)}`;
  return `<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="${csp}">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="Lax — an archive of formalized mathematical concepts and their proofs">
<title>${esc(shell.title)}</title>
<link rel="icon" href="${FAVICON}" type="image/svg+xml">
<link rel="stylesheet" href="${stylesheet("katex.css")}">
<link rel="stylesheet" href="${stylesheet("style.css")}">
</head><body>
<header class="site-header">
  <button id="sidebar-toggle" class="sidebar-toggle" type="button" aria-expanded="false" aria-label="Toggle sidebar"><span class="sidebar-toggle-icon"></span></button>
  <h1 class="site-title"><a href="${root}index.html">Lax <span class="site-title-quiet">Lean Archive</span></a></h1>
  <nav class="header-actions" aria-label="Contribution and account">
    <a class="header-submit" href="${root}contributing.html">Submit</a>
    ${accountUi()}
  </nav>
</header>
<main id="content-shell">
<div class="sidebar-backdrop" id="sidebar-backdrop"></div>
<aside id="sidebar">
${shell.sidebar}
</aside>
<section id="main"><div id="detail">
${shell.content}
</div></section>
</main>
${accountDialog()}
${scripts}
</body></html>
`;
}

// ---- badges and pills ----

const TYPE_BADGES: Record<string, string> = {
  theorem: "thm",
  definition: "def",
  lemma: "lem",
  corollary: "cor",
  proposition: "prp",
};

/** The 3-letter badge for a concept `type`. A missing type is pre-gate data
 * (the annotation gate requires one), never something to render around. */
export function typeBadgeText(type?: string): string {
  const key = type?.trim().toLowerCase() ?? "";
  if (key === "") throw new Error("concept type is required; the annotation gate enforces it");
  return TYPE_BADGES[key] ?? key.slice(0, 3);
}

export function typeBadge(type?: string, proven?: boolean): string {
  const status = proven === undefined ? "" : proven ? "proven" : "open";
  const title = [type, status ? `${status}. ${HONESTY_TOOLTIP}` : ""].filter(Boolean).join(" — ");
  const cls = `type-badge${status ? ` ${status}` : ""}`;
  return `<span class="${cls}"${title ? ` title="${attr(title)}"` : ""}>${esc(typeBadgeText(type))}${proven === undefined ? "" : proven ? "✓" : "×"}</span>`;
}

/** The proof marker: the turnstile boxed as a chip, visually parallel to the
 * type badge and echoing the proof node of the network figure. */
export function proofBadge(): string {
  return `<span class="proof-badge" role="img" aria-label="proof">⊢</span>`;
}

/** A concept's aggregate status, without statement counts. */
export function countsPill(proven: number, total: number): string {
  if (total === 0)
    return `<span class="status-pill pill-none">definition</span>`;
  const cls = proven === total ? "pill-proven" : "pill-partial";
  return `<span class="status-pill ${cls}" title="${attr(HONESTY_TOOLTIP)}">${proven === total ? "proven" : "open"}</span>`;
}

export function statePill(state: string): string {
  return `<span class="status-pill state-${esc(state)}">${esc(state)}</span>`;
}

export function code(value: string): string { return `<code>${esc(value)}</code>`; }

export function formatDate(value?: string): string {
  if (!value) return "—";
  const date = new Date(value);
  return Number.isNaN(date.valueOf()) ? esc(value) : date.toISOString().slice(0, 10);
}

export function plural(n: number, one: string, many = `${one}s`): string {
  return `${n} ${n === 1 ? one : many}`;
}
