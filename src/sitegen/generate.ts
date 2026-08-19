import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { copyAssets } from "./assets.js";
import { MarkdownRenderer } from "./markdown.js";
import { SiteModel, type SiteSubmission } from "./model.js";
import { conceptPage } from "./pages/concept.js";
import { contentPage } from "./pages/content.js";
import { indexPage } from "./pages/index.js";
import { openProblemsPage } from "./pages/open-problems.js";
import { proofPage } from "./pages/proof.js";
import { submissionPage } from "./pages/submission.js";

export type { SiteSubmission } from "./model.js";

/** Generate a deterministic, fully static archive website into outDir. */
export async function generateSite(submissions: SiteSubmission[], outDir: string): Promise<void> {
  const model = new SiteModel(submissions);
  const context = { model, markdown: new MarkdownRenderer(model) };
  const files = new Map<string, string>();
  files.set("index.html", await indexPage(context));
  files.set("contributing.html", contentPage(context, "contributing", "Contributing"));
  const proofObligations = openProblemsPage(context);
  files.set("open-proof-obligations.html", proofObligations);
  // Preserve shared preview and production links published under the old name.
  files.set("open-problems.html", proofObligations);
  for (const submission of model.submissions) {
    files.set(path.join(submission.record.id, "index.html"), submissionPage(context, submission));
    if (!submission.output) continue;
    for (const concept of submission.output.concepts) {
      const located = model.conceptHome.get(concept.id)!;
      files.set(path.join(submission.record.id, `${concept.id}.html`), await conceptPage(context, located));
    }
    for (const proof of submission.output.proofs) {
      // Concept and proof packages have distinct names, so ids cannot collide.
      const file = path.join(submission.record.id, `${proof.id}.html`);
      if (files.has(file)) throw new Error(`proof page ${file} collides with an existing page`);
      files.set(file, proofPage(context, model.proofHome.get(proof.id)!));
    }
  }
  // Submission pages are cached independently by GitHub Pages' CDN. Point
  // every link at a digest of the complete unversioned render, so changes to
  // either archive data or website templates get a fresh, coherent cache key.
  const siteVersion = createHash("sha256")
    .update([...files].sort(([a], [b]) => a.localeCompare(b)).map(([file, content]) => `${file}\0${content}\0`).join(""), "utf8")
    .digest("hex")
    .slice(0, 16);
  for (const [relative, content] of files)
    files.set(relative, versionSubmissionLinks(content, relative, model, siteVersion));
  const outputRoot = path.resolve(outDir);
  const renderedFiles = [...files]
    .sort(([a], [b]) => a.localeCompare(b))
    .map(([relative, content]) => [siteOutputPath(outputRoot, relative), content] as const);
  // Build all content before replacing the old site, minimizing partial output.
  fs.rmSync(outputRoot, { recursive: true, force: true });
  fs.mkdirSync(outputRoot, { recursive: true });
  copyAssets(outputRoot);
  for (const [file, content] of renderedFiles) {
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, content);
  }
}

function versionSubmissionLinks(content: string, pagePath: string, model: SiteModel, siteVersion: string): string {
  const versionHref = (href: string): string => {
    if (!href || href.startsWith("#") || /(?:^|[?&])v=/.test(href)) return href;
    let resolved: URL;
    try {
      resolved = new URL(href.replace(/&amp;/g, "&"), `https://archive.invalid/${pagePath.replaceAll(path.sep, "/")}`);
    } catch {
      return href;
    }
    if (resolved.origin !== "https://archive.invalid") return href;
    const target = resolved.pathname.split("/").filter(Boolean)[0];
    if (!target) return href;
    if (!model.submissionById.get(decodeURIComponent(target))?.output) return href;
    const hashAt = href.indexOf("#");
    const base = hashAt < 0 ? href : href.slice(0, hashAt);
    const fragment = hashAt < 0 ? "" : href.slice(hashAt);
    const separator = base.includes("?") ? (base.includes("&amp;") ? "&amp;" : "&") : "?";
    return `${base}${separator}v=${siteVersion}${fragment}`;
  };
  return content
    .replace(/(\bhref=")([^"]+)(")/g, (_all, before: string, href: string, after: string) =>
      `${before}${versionHref(href)}${after}`)
    .replace(/("href":")([^"]+)(")/g, (_all, before: string, href: string, after: string) =>
      `${before}${versionHref(href)}${after}`);
}

function siteOutputPath(outputRoot: string, relative: string): string {
  const file = path.resolve(outputRoot, relative);
  if (file === outputRoot || !file.startsWith(`${outputRoot}${path.sep}`)) {
    throw new Error(`generated page escapes the site output directory: ${relative}`);
  }
  return file;
}
