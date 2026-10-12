import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
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
import { indexPage, landingLeanModel } from "./pages/index.js";
import { notFoundPage } from "./pages/not-found.js";
import { openProblemsPage } from "./pages/open-problems.js";
import { paperPage, paperPdfPage } from "./pages/paper.js";
import { proofPage } from "./pages/proof.js";
import { INTRO_SUBMISSION_ID } from "./pages/shared.js";
import { submissionPage } from "./pages/submission.js";
import { submissionsPage } from "./pages/submissions.js";
import { workshopPage } from "./pages/workshop.js";
import { createGraphPreparationSession, type GraphPreparationOptions, type GraphPreparationResult } from "./graph-prepare.js";
import { loadLeanCode } from "./lean-code.js";
import type { SkippedRecord } from "../types.js";

export type { SiteSubmission } from "./model.js";
export type { SkippedRecord } from "../types.js";

export interface GenerateOptions {
  /** Prepared compiler information; no Lean process runs in the renderer. */
  leanCode?: { cacheDir: string; required?: boolean };
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
  /** Requests an in-memory detailed report for library callers. For large
   * builds use graphs.reportFile, which streams details outside the site. */
  graphReport?: (report: GraphPreparationResult) => void;
  /**
   * Where a record the generator could not render is reported. The record
   * is left out and the site is rendered again without it; the default
   * reports through `log`, so a skip is never silent.
   */
  onSkip?: (skipped: SkippedRecord) => void;
  /**
   * Which records get their own pages — the submission, concept, proof and
   * paper pages under `<id>/`. Every record stays in the model, so the
   * listings, the graphs, the sidebars and the machine index still cover
   * the whole archive; only the pages of the records outside the selection
   * are not written, and a link to one of them leads off the output.
   * `dependencies` adds the transitive dependencies of the selected ids.
   * Meant for `lax serve`, which previews one folder against an archive of
   * thousands of pages the author will not open. Absent: every record.
   */
  pages?: { ids: readonly string[]; dependencies?: boolean };
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
  const outputRoot = path.resolve(outDir);
  const graphMode = settings.graphs?.mode ?? "local";
  const graphOptions: GraphPreparationOptions = {
    mode: graphMode, cacheDir: path.resolve(".lax-graph-cache"),
    collectDetails: Boolean(settings.graphReport), ...settings.graphs,
    measurement: { ...(graphMode === "local" && !process.env.GRAPH_CHROME && !settings.graphs?.measurement?.executablePath
      ? { hostBrowser: false } : {}), ...settings.graphs?.measurement },
  };
  if (graphOptions.reportFile) {
    const report = path.resolve(graphOptions.reportFile);
    if (report === outputRoot || report.startsWith(outputRoot + path.sep))
      throw new Error("graph report must be outside the published site");
  }
  fs.mkdirSync(path.dirname(outputRoot), { recursive: true });
  const excluded = new Set<string>();
  let remaining = submissions;
  for (;;) {
    // A whole attempt has its own staging directory. Neither partially
    // prepared pages nor pages of an excluded record can reach publication.
    const staged = fs.mkdtempSync(path.join(path.dirname(outputRoot), `.${path.basename(outputRoot)}-build-`));
    const previous = `${staged}-previous`;
    let movedPrevious = false, installed = false;
    let session: ReturnType<typeof createGraphPreparationSession> | undefined;
    try {
      session = createGraphPreparationSession(graphOptions);
      const written = new Set<string>(), sharedHashes = new Map<string, string>();
      const write = (relative: string, content: string | Buffer, shared = false) => {
        const file = siteOutputPath(staged, relative);
        const digest = shared ? createHash("sha256").update(content).digest("hex") : undefined;
        if (written.has(relative)) {
          if (shared && sharedHashes.get(relative) === digest) return;
          throw new Error(`generated file ${relative} written twice with different contents`);
        }
        fs.mkdirSync(path.dirname(file), { recursive: true });
        fs.writeFileSync(file, content);
        written.add(relative);
        if (digest) sharedHashes.set(relative, digest);
      };
      for await (const output of renderPages(remaining, settings.epoch, log, settings.leanCode, settings.pages)) {
        if ("sourceFile" in output) {
          const file = siteOutputPath(staged, output.relative);
          if (written.has(output.relative)) throw new Error(`generated file ${output.relative} written twice`);
          fs.mkdirSync(path.dirname(file), { recursive: true });
          fs.copyFileSync(output.sourceFile, file);
          written.add(output.relative);
        } else if (output.relative.endsWith(".html")) {
          for (const [relative, content] of await session.prepare(output.relative, output.content))
            write(relative, content, relative !== output.relative);
        } else write(output.relative, output.content, output.shared);
      }
      const prepared = session.finish();
      settings.graphReport?.(prepared);
      await session.close();
      copyAssets(staged, { localGraphs: prepared.localFallback });
      if (fs.existsSync(outputRoot)) { fs.renameSync(outputRoot, previous); movedPrevious = true; }
      try { fs.renameSync(staged, outputRoot); installed = true; }
      catch (error) {
        if (movedPrevious) { fs.renameSync(previous, outputRoot); movedPrevious = false; }
        throw error;
      }
      return;
    } catch (error) {
      // Only producer errors attributed by renderPages exclude a record.
      // Graph validation, measurement, reporting and disk failures stay fatal.
      if (!(error instanceof RecordError) || excluded.has(error.recordId)) throw error;
      excluded.add(error.recordId);
      skip({ id: error.recordId, reason: error.message });
      remaining = remaining.filter((submission) => submission.record.id !== error.recordId);
    } finally {
      try { await session?.close(); }
      finally {
        if (!installed) fs.rmSync(staged, { recursive: true, force: true });
        if (installed && movedPrevious) fs.rmSync(previous, { recursive: true, force: true });
      }
    }
  }
}

/** The records whose pages a selection asks for: the ids named, plus —
 * with `dependencies` — every record they transitively build on, as the
 * model resolved the requires. Ids the model does not hold are ignored. */
function pagesToRender(model: SiteModel, pages: NonNullable<GenerateOptions["pages"]>): Set<string> {
  const rendered = new Set<string>();
  for (const id of pages.ids) {
    if (!model.submissionById.has(id)) continue;
    rendered.add(id);
    if (pages.dependencies) for (const upstream of model.submissionUpstream(id)) rendered.add(upstream);
  }
  return rendered;
}

type RenderedFile = { relative: string; content: string | Buffer; shared?: boolean }
  | { relative: string; sourceFile: string };

/** Yield each page before composing the next. The file-name inventory is
 * small; page bodies, PDFs and generated assets are never kept archive-wide. */
async function* renderPages(
  submissions: SiteSubmission[],
  epoch: string | undefined,
  log: (line: string) => void,
  leanCode?: GenerateOptions["leanCode"],
  pages?: GenerateOptions["pages"],
): AsyncGenerator<RenderedFile> {
  const model = new SiteModel(submissions, epoch);
  const rendered = pages === undefined ? undefined : pagesToRender(model, pages);
  if (leanCode) {
    loadLeanCode(model, leanCode.cacheDir, leanCode.required);
    const examples = landingLeanModel();
    loadLeanCode(examples, leanCode.cacheDir, leanCode.required);
    for (const [id, data] of examples.leanCode) model.leanCode.set(`example:${id}`, data);
  }
  const context = { model, markdown: new MarkdownRenderer(model) };
  // The header's "Introduction" leads into the introduction's paper, once
  // the archive holds it.
  const intro = model.submissions.find((submission) => submission.record.id === INTRO_SUBMISSION_ID && submission.output?.paper);
  configureSiteNav({ introduction: intro ? `${intro.record.id}/paper.html` : undefined });
  const files = new Set<string>();
  const emit = (relative: string, content: string | Buffer): RenderedFile => {
    files.add(relative);
    return { relative, content };
  };
  yield emit("index.html", await indexPage(context));
  yield emit(path.join("submissions", "index.html"), submissionsPage(context));
  // The machine-readable pair, documented in content/contributing.md. Two
  // spaces and a trailing newline: these are files people read as well.
  yield emit("index.json", `${JSON.stringify(recordIndex(model), null, 2)}\n`);
  yield emit("environments.json", `${JSON.stringify(environmentIndex(model), null, 2)}\n`);
  yield emit(path.join("all-comments", "index.html"), allCommentsPage(context));
  yield emit("about.html", await contentPage(context, "about", "About Lax"));
  yield emit("contributing.html", await contentPage(context, "contributing", "Getting started"));
  yield emit("impressum.html", await contentPage(context, "impressum", "Imprint"));
  yield emit("privacy.html", await contentPage(context, "privacy", "Privacy Notice"));
  yield emit(path.join("workshop", "index.html"), workshopPage(context));
  {
    const proofObligations = openProblemsPage(context);
    yield emit("open-proof-obligations.html", proofObligations);
    // Preserve shared preview and production links published under the old name.
    yield emit("open-problems.html", proofObligations);
  }
  // Served by GitHub Pages for any address that does not exist; deleted
  // records land here rather than on GitHub's generic error page.
  yield emit("404.html", notFoundPage());
  for (const submission of model.submissions) {
    if (rendered !== undefined && !rendered.has(submission.record.id)) continue;
    try {
      for await (const output of renderRecord(context, submission, log)) {
        if (files.has(output.relative) && "content" in output && !output.shared)
          throw new Error(`generated page ${output.relative} collides with an existing page`);
        files.add(output.relative);
        yield output;
      }
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
  const indexed = [...files].filter((relative) =>
    relative.endsWith(".html") && relative !== "404.html" && relative !== "open-problems.html" && !unlisted.has(relative.split(path.sep)[0]!));
  yield emit("robots.txt", robotsTxt());
  yield emit("sitemap.xml", sitemapXml(indexed));
}

/** One record's pages: its own, one per concept and proof, and its paper's. */
async function* renderRecord(
  context: { model: SiteModel; markdown: MarkdownRenderer },
  submission: SiteSubmission,
  log: (line: string) => void,
): AsyncGenerator<RenderedFile> {
  const { model } = context;
  const emit = (relative: string, content: string | Buffer): RenderedFile => ({ relative, content });
  yield emit(path.join(submission.record.id, "index.html"), submissionPage(context, submission));
  if (!submission.output) return;
  for (const concept of submission.output.concepts) {
    const located = model.conceptHome.get(concept.id)!;
    yield emit(path.join(submission.record.id, `${concept.id}.html`), await conceptPage(context, located));
  }
  for (const proof of submission.output.proofs) {
    // Concept and proof packages have distinct names, so ids cannot collide.
    const file = path.join(submission.record.id, `${proof.id}.html`);
    yield emit(file, proofPage(context, model.proofHome.get(proof.id)!));
  }
  // The paper page exists for every declared paper: the reflowed text
  // when the bundle passed the schema gate, the paper as printed
  // otherwise. The PDF, and the printed page under its own address, only
  // when the papers cache supplied the bytes (production, not previews).
  if (submission.output.paper) {
    const web = preparePaperWeb(submission, log);
    yield emit(path.join(submission.record.id, "paper.html"), await paperPage(context, submission, web?.page));
    for (const [relative, content] of web?.files ?? []) yield { relative, content, shared: true };
    if (submission.paperFile) {
      yield emit(path.join(submission.record.id, "paper-pdf.html"), await paperPdfPage(context, submission, web !== undefined));
      yield { relative: path.join(submission.record.id, "paper.pdf"), sourceFile: submission.paperFile };
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
