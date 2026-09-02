import fs from "node:fs";
import path from "node:path";
import { copyAssets } from "./assets.js";
import { MarkdownRenderer } from "./markdown.js";
import { SiteModel, type SiteSubmission } from "./model.js";
import { preparePaperWeb } from "./paper-web.js";
import { conceptPage } from "./pages/concept.js";
import { allCommentsPage } from "./pages/all-comments.js";
import { contentPage } from "./pages/content.js";
import { indexPage } from "./pages/index.js";
import { openProblemsPage } from "./pages/open-problems.js";
import { paperPage } from "./pages/paper.js";
import { proofPage } from "./pages/proof.js";
import { submissionPage } from "./pages/submission.js";

export type { SiteSubmission } from "./model.js";

export interface GenerateOptions {
  /** Where schema-gate drops (a paper page falling back to PDF-only) are
   * reported. Defaults to console.warn so production builds always say so. */
  log?: (line: string) => void;
}

/** Generate a deterministic, fully static archive website into outDir. */
export async function generateSite(submissions: SiteSubmission[], outDir: string, options: GenerateOptions = {}): Promise<void> {
  const log = options.log ?? ((line: string) => console.warn(line));
  const model = new SiteModel(submissions);
  const context = { model, markdown: new MarkdownRenderer(model) };
  const files = new Map<string, string | Buffer>();
  /** Content-addressed outputs (hashed fonts) may be shared between records;
   * the same path must always carry the same bytes. */
  const addFile = (relative: string, content: Buffer): void => {
    const existing = files.get(relative);
    if (existing !== undefined) {
      if (Buffer.isBuffer(existing) && existing.equals(content)) return;
      throw new Error(`generated file ${relative} written twice with different contents`);
    }
    files.set(relative, content);
  };
  files.set("index.html", await indexPage(context));
  files.set(path.join("all-comments", "index.html"), allCommentsPage(context));
  files.set("contributing.html", contentPage(context, "contributing", "Getting started"));
  files.set("impressum.html", contentPage(context, "impressum", "Imprint"));
  files.set("privacy.html", contentPage(context, "privacy", "Privacy Notice"));
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
    // The paper page exists for every declared paper; the PDF beside it only
    // when the papers cache supplied the bytes (production, not previews),
    // and the reflow surface only when the bundle passed the schema gate.
    if (submission.output.paper) {
      const web = preparePaperWeb(submission, log);
      files.set(path.join(submission.record.id, "paper.html"), await paperPage(context, submission, web?.page));
      for (const [relative, content] of web?.files ?? []) addFile(relative, content);
      if (submission.paperFile)
        files.set(path.join(submission.record.id, "paper.pdf"), fs.readFileSync(submission.paperFile));
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
