import fs from "node:fs";
import path from "node:path";
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

function siteOutputPath(outputRoot: string, relative: string): string {
  const file = path.resolve(outputRoot, relative);
  if (file === outputRoot || !file.startsWith(`${outputRoot}${path.sep}`)) {
    throw new Error(`generated page escapes the site output directory: ${relative}`);
  }
  return file;
}
