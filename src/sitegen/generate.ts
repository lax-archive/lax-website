import fs from "node:fs";
import path from "node:path";
import { copyAssets } from "./assets.js";
import { robotsTxt, sitemapXml } from "./crawlers.js";
import { environmentIndex, recordIndex } from "./machine-index.js";
import { MarkdownRenderer } from "./markdown.js";
import { isDiscoverableSubmission, RecordError, SiteModel, type SiteSubmission } from "./model.js";
import { preparePaperWeb } from "./paper-web.js";
import { conceptPage } from "./pages/concept.js";
import { allCommentsPage } from "./pages/all-comments.js";
import { contentPage } from "./pages/content.js";
import { configureSiteNav } from "./html.js";
import { indexPage } from "./pages/index.js";
import { notFoundPage } from "./pages/not-found.js";
import { openProblemsPage } from "./pages/open-problems.js";
import { paperPage, paperPdfPage } from "./pages/paper.js";
import { proofPage } from "./pages/proof.js";
import { INTRO_SUBMISSION_ID } from "./pages/shared.js";
import { submissionPage } from "./pages/submission.js";
import { prepareGraphs, type GraphPreparationOptions, type GraphPreparationResult } from "./graph-prepare.js";
import { compareText } from "../graph-layout/normalize.js";
import type { SkippedRecord } from "../types.js";

export type { SiteSubmission } from "./model.js";
export type { SkippedRecord } from "../types.js";

export interface GenerateOptions {
  /** Where schema-gate drops (a paper page falling back to PDF-only) are
   * reported. Defaults to console.warn so production builds always say so. */
  log?: (line: string) => void;
  /**
   * The archive's epoch — the environment this year's submissions are
   * recommended to be written in. Defaults to `EPOCH` in `src/config.ts`.
   * `lax serve` passes the epoch its own environment table names, because a
   * pinned renderer's config is as old as the release that carried it.
   */
  epoch?: string;
  /** Public CLI builds explicitly select archive mode. Older packaged local
   * callers keep browser-free installation and the isolated local worker. */
  graphs?: GraphPreparationOptions;
  /** Build diagnostics/performance stay outside deterministic published data. */
  graphReport?: (report: GraphPreparationResult) => void;
  /**
   * Where a record the generator could not render is reported. The record
   * is left out and the site is rendered again without it; the default
   * reports through `log`, so a skip is never silent.
   */
  onSkip?: (skipped: SkippedRecord) => void;
}

/**
 * Generate a deterministic, fully static archive website into outDir.
 *
 * The third argument may be the epoch id on its own: that is the shape `lax
 * serve` calls with, and it is the whole reason the options bag is not the
 * only form. A caller that passes nothing (an older CLI) gets the config's
 * epoch, which is correct until the year it is not.
 */
export async function generateSite(
  submissions: SiteSubmission[],
  outDir: string,
  options: GenerateOptions | string = {},
): Promise<void> {
  const settings = typeof options === "string" ? { epoch: options } : options;
  const log = settings.log ?? ((line: string) => console.warn(line));
  const skip = settings.onSkip ?? ((skipped: SkippedRecord) => log(`skipping ${skipped.id}: ${skipped.reason}`));
  // The per-record boundary. A failure the model or a record's pages can
  // pin on one record drops that record and renders again without it — the
  // pages are a function of the list, and the listings and graphs embed
  // every record, so a partial render is not an option. A failure nothing
  // can attribute still fails the build: the alternative is guessing.
  const excluded = new Set<string>();
  let remaining = submissions;
  let files: Map<string, string | Buffer>;
  for (;;) {
    try {
      files = await renderPages(remaining, settings.epoch, log);
      break;
    } catch (error) {
      if (!(error instanceof RecordError) || excluded.has(error.recordId)) throw error;
      excluded.add(error.recordId);
      skip({ id: error.recordId, reason: error.message });
      remaining = remaining.filter((submission) => submission.record.id !== error.recordId);
    }
  }
  const outputRoot = path.resolve(outDir);
  const graphMode = settings.graphs?.mode ?? "local";
  const prepared = await prepareGraphs(files, {
    mode: graphMode, cacheDir: path.resolve(".lax-graph-cache"), ...settings.graphs,
    measurement: { ...(graphMode === "local" && !process.env.GRAPH_CHROME && !settings.graphs?.measurement?.executablePath
      ? { hostBrowser: false } : {}), ...settings.graphs?.measurement },
  });
  settings.graphReport?.(prepared);
  const renderedFiles = [...files].sort(([a], [b]) => compareText(a, b));
  for (const [relative] of renderedFiles) siteOutputPath(outputRoot, relative);
  // Finish writes and asset packaging alongside the old output. A failed
  // measurement, validator, missing asset or full disk keeps the old site.
  fs.mkdirSync(path.dirname(outputRoot), { recursive: true });
  const staged = fs.mkdtempSync(path.join(path.dirname(outputRoot), `.${path.basename(outputRoot)}-build-`));
  const previous = `${staged}-previous`;
  let movedPrevious = false, installed = false;
  try {
    copyAssets(staged, { localGraphs: prepared.localFallback });
    for (const [relative, content] of renderedFiles) {
      const file = siteOutputPath(staged, relative);
      fs.mkdirSync(path.dirname(file), { recursive: true });
      fs.writeFileSync(file, content);
    }
    if (fs.existsSync(outputRoot)) { fs.renameSync(outputRoot, previous); movedPrevious = true; }
    try { fs.renameSync(staged, outputRoot); installed = true; }
    catch (error) {
      if (movedPrevious) { fs.renameSync(previous, outputRoot); movedPrevious = false; }
      throw error;
    }
  } finally {
    if (!installed) fs.rmSync(staged, { recursive: true, force: true });
    if (installed && movedPrevious) fs.rmSync(previous, { recursive: true, force: true });
  }
}

/** Every page of the site, before graph preparation, keyed by output path. */
async function renderPages(
  submissions: SiteSubmission[],
  epoch: string | undefined,
  log: (line: string) => void,
): Promise<Map<string, string | Buffer>> {
  const model = new SiteModel(submissions, epoch);
  const context = { model, markdown: new MarkdownRenderer(model) };
  // The header's "Introduction" leads into the introduction's paper, once
  // the archive holds it.
  const intro = model.submissions.find((submission) => submission.record.id === INTRO_SUBMISSION_ID && submission.output?.paper);
  configureSiteNav({ introduction: intro ? `${intro.record.id}/paper.html` : undefined });
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
  // The machine-readable pair, documented in content/contributing.md. Two
  // spaces and a trailing newline: these are files people read as well.
  files.set("index.json", `${JSON.stringify(recordIndex(model), null, 2)}\n`);
  files.set("environments.json", `${JSON.stringify(environmentIndex(model), null, 2)}\n`);
  files.set(path.join("all-comments", "index.html"), allCommentsPage(context));
  files.set("about.html", await contentPage(context, "about", "About Lax"));
  files.set("contributing.html", await contentPage(context, "contributing", "Getting started"));
  files.set("impressum.html", await contentPage(context, "impressum", "Imprint"));
  files.set("privacy.html", await contentPage(context, "privacy", "Privacy Notice"));
  const proofObligations = openProblemsPage(context);
  files.set("open-proof-obligations.html", proofObligations);
  // Preserve shared preview and production links published under the old name.
  files.set("open-problems.html", proofObligations);
  // Served by GitHub Pages for any address that does not exist; deleted
  // records land here rather than on GitHub's generic error page.
  files.set("404.html", notFoundPage());
  for (const submission of model.submissions) {
    try {
      await renderRecord(context, submission, files, addFile, log);
    } catch (error) {
      if (error instanceof RecordError) throw error;
      const message = error instanceof Error ? error.message : String(error);
      throw new RecordError(submission.record.id, message, { cause: error });
    }
  }
  // What crawlers get: everything but the branch previews, and the sitemap
  // of every page the build wrote for a listed record — the unlisted keep
  // their canonical links and stay out of the listing, as everywhere else.
  const unlisted = new Set(model.submissions.filter((submission) => !isDiscoverableSubmission(submission)).map((submission) => submission.record.id));
  const indexed = [...files.keys()].filter((relative) =>
    relative.endsWith(".html") && relative !== "404.html" && relative !== "open-problems.html" && !unlisted.has(relative.split(path.sep)[0]!));
  files.set("robots.txt", robotsTxt());
  files.set("sitemap.xml", sitemapXml(indexed));
  return files;
}

/** One record's pages: its own, one per concept and proof, and its paper's. */
async function renderRecord(
  context: { model: SiteModel; markdown: MarkdownRenderer },
  submission: SiteSubmission,
  files: Map<string, string | Buffer>,
  addFile: (relative: string, content: Buffer) => void,
  log: (line: string) => void,
): Promise<void> {
  const { model } = context;
  files.set(path.join(submission.record.id, "index.html"), submissionPage(context, submission));
  if (!submission.output) return;
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
  // The paper page exists for every declared paper: the reflowed text
  // when the bundle passed the schema gate, the paper as printed
  // otherwise. The PDF, and the printed page under its own address, only
  // when the papers cache supplied the bytes (production, not previews).
  if (submission.output.paper) {
    const web = preparePaperWeb(submission, log);
    files.set(path.join(submission.record.id, "paper.html"), await paperPage(context, submission, web?.page));
    for (const [relative, content] of web?.files ?? []) addFile(relative, content);
    if (submission.paperFile) {
      files.set(path.join(submission.record.id, "paper-pdf.html"), await paperPdfPage(context, submission, web !== undefined));
      files.set(path.join(submission.record.id, "paper.pdf"), fs.readFileSync(submission.paperFile));
    }
  }
}

function siteOutputPath(outputRoot: string, relative: string): string {
  const file = path.resolve(outputRoot, relative);
  if (file === outputRoot || !file.startsWith(`${outputRoot}${path.sep}`)) {
    throw new Error(`generated page escapes the site output directory: ${relative}`);
  }
  return file;
}
