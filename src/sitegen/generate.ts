import fs from "node:fs";
import path from "node:path";
import { copyAssets } from "./assets.js";
import { MarkdownRenderer } from "./markdown.js";
import { SiteModel, type SiteSubmission } from "./model.js";
import { conceptPage } from "./pages/concept.js";
import { contentPage } from "./pages/content.js";
import { indexPage } from "./pages/index.js";
import { proofPage } from "./pages/proof.js";
import { submissionPage } from "./pages/submission.js";

export type { SiteSubmission } from "./model.js";

/** Generate a deterministic, fully static archive website into outDir. */
export async function generateSite(submissions: SiteSubmission[], outDir: string): Promise<void> {
  const model = new SiteModel(submissions);
  const context = { model, markdown: new MarkdownRenderer(model) };
  const files = new Map<string, string>();
  files.set("index.html", indexPage(context));
  files.set("contributing.html", contentPage(context, "contributing", "Contributing"));
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
  // Build all content before replacing the old site, minimizing partial output.
  fs.rmSync(outDir, { recursive: true, force: true });
  fs.mkdirSync(outDir, { recursive: true });
  copyAssets(outDir);
  for (const [relative, content] of [...files].sort(([a], [b]) => a.localeCompare(b))) {
    const file = path.join(outDir, relative);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, content);
  }
}
