import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";

function previewSlug(branch) {
  const readable = branch
    .normalize("NFKD")
    .toLowerCase()
    .replaceAll("/", "--")
    .replace(/[^a-z0-9._-]+/g, "-")
    .replace(/^[.-]+|[.-]+$/g, "")
    .slice(0, 56) || "branch";
  const digest = crypto.createHash("sha256").update(branch).digest("hex").slice(0, 8);
  return `${readable}-${digest}`;
}

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function previewDirectory(root, branch) {
  return path.join(path.resolve(root), "previews", previewSlug(branch));
}

function recordPreview(root, branch, sha) {
  const directory = previewDirectory(root, branch);
  if (!fs.existsSync(directory)) throw new Error(`preview output does not exist: ${directory}`);
  const record = {
    branch,
    sha,
    updatedAt: new Date().toISOString(),
  };
  fs.writeFileSync(path.join(directory, "preview.json"), `${JSON.stringify(record, null, 2)}\n`);
}

function previewRecords(previewsRoot) {
  if (!fs.existsSync(previewsRoot)) return [];
  return fs.readdirSync(previewsRoot, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => {
      const file = path.join(previewsRoot, entry.name, "preview.json");
      if (!fs.existsSync(file)) return undefined;
      const record = JSON.parse(fs.readFileSync(file, "utf8"));
      return { ...record, slug: entry.name };
    })
    .filter(Boolean)
    .sort((a, b) => a.branch.localeCompare(b.branch));
}

function buildIndex(root) {
  const previewsRoot = path.join(path.resolve(root), "previews");
  fs.mkdirSync(previewsRoot, { recursive: true });
  const cards = previewRecords(previewsRoot).map((record) => {
    const shortSha = String(record.sha).slice(0, 7);
    const updated = new Date(record.updatedAt);
    const date = Number.isNaN(updated.valueOf()) ? "" : updated.toISOString().slice(0, 16).replace("T", " ") + " UTC";
    return `<li><a href="./${encodeURIComponent(record.slug)}/"><strong>${escapeHtml(record.branch)}</strong><span>${escapeHtml(shortSha)}${date ? ` · ${escapeHtml(date)}` : ""}</span></a></li>`;
  }).join("\n");
  const empty = `<p class="empty">No branch previews are published yet.</p>`;
  const html = `<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Lax branch previews</title>
<style>
:root{ color-scheme:light; font-family:Georgia,serif; color:#2b2b2b; background:#f8f6f3 }
body{ max-width:52rem; margin:0 auto; padding:4rem 1.25rem }
h1{ margin:0 0 .35rem; font-weight:500; font-variant:small-caps; letter-spacing:.04em }
p{ color:#6b7280; line-height:1.55 }
ul{ display:grid; gap:.75rem; margin:2rem 0; padding:0; list-style:none }
a{ display:flex; justify-content:space-between; gap:1rem; padding:1rem 1.1rem; color:#2c5f8a; background:#fff; border:1px solid #d6d0c8; border-radius:7px; text-decoration:none }
a:hover,a:focus-visible{ border-color:#3b6b9a; outline:3px solid #e9f0f7 }
a span{ color:#6b7280; font-family:ui-monospace,monospace; font-size:.78rem; white-space:nowrap }
.empty{ margin-top:2rem; padding:1rem; background:#fff; border:1px solid #e8e3dc; border-radius:7px }
@media(max-width:36rem){ a{ flex-direction:column } }
</style>
</head><body>
<h1>Lax branch previews</h1>
<p>Shareable builds of work in progress. Each preview updates when its branch is pushed and disappears when that branch is deleted.</p>
${cards ? `<ul>${cards}</ul>` : empty}
</body></html>
`;
  fs.writeFileSync(path.join(previewsRoot, "index.html"), html);
}

const [command, ...args] = process.argv.slice(2);
if (command === "slug" && args.length === 1) process.stdout.write(previewSlug(args[0]));
else if (command === "record" && args.length === 3) recordPreview(...args);
else if (command === "index" && args.length === 1) buildIndex(args[0]);
else {
  console.error("usage: pages-previews.mjs slug <branch> | record <pages-root> <branch> <sha> | index <pages-root>");
  process.exitCode = 2;
}
