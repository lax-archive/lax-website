// The page shell and small html helpers, following the reference design:
// sticky header (hamburger + centered title), collapsible sidebar with
// search/filters, and a single content pane. Only sidebar.js, layout.js and
// dag.js run in the browser; everything else is rendered at build time.

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

const CSP =
  "default-src 'none'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src https: data:; font-src 'self'";

// Inline data: URI so the icon loads under the CSP everywhere — including
// plain-http `lax serve`, where an assets/ file would violate `img-src`.
const FAVICON = "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Crect width='64' height='64' rx='12' fill='%232a7f8f'/%3E%3Cpath d='M18 14v36h29v-8H27V14z' fill='%23fff'/%3E%3C/svg%3E";

export function page(shell: PageShell): string {
  const root = shell.rootRel;
  const scripts = ["assets/sidebar.js", ...(shell.scripts ?? [])]
    .map((src) => `<script src="${attr(root + src)}"></script>`)
    .join("\n");
  return `<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="${CSP}">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="Lax — an archive of formalized mathematical concepts and their proofs">
<title>${esc(shell.title)}</title>
<link rel="icon" href="${FAVICON}" type="image/svg+xml">
<link rel="stylesheet" href="${root}assets/katex.css">
<link rel="stylesheet" href="${root}assets/style.css">
</head><body>
<header class="site-header">
  <button id="sidebar-toggle" class="sidebar-toggle" type="button" aria-expanded="false" aria-label="Toggle sidebar"><span class="sidebar-toggle-icon"></span></button>
  <h1 class="site-title"><a href="${root}index.html">Lax <span class="site-title-quiet">Lean Archive</span></a></h1>
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
