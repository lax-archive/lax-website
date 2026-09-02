import fs from "node:fs";
import path from "node:path";
import { bundleCachePath } from "./bundles.js";
import { paperCachePath } from "./papers.js";
import type { BuildOutput, DbRecord, PaperEntry, PaperMark, PaperMarkPoint, PaperWebEntry } from "./types.js";
import type { SiteSubmission } from "./sitegen/model.js";

function readJson<T>(file: string): T | undefined {
  if (!fs.existsSync(file)) return undefined;
  return JSON.parse(fs.readFileSync(file, "utf8")) as T;
}

function isObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

const SHA256_HEX = /^[0-9a-f]{64}$/u;
const MAX_PAPER_PAGES = 500;
const MAX_PAPER_MARKS = 10_000;

function positiveInteger(value: unknown, label: string): number {
  if (typeof value !== "number" || !Number.isInteger(value) || value < 1)
    throw new Error(`${label} must be a positive integer`);
  return value;
}

function finiteNumber(value: unknown, label: string): number {
  if (typeof value !== "number" || !Number.isFinite(value) || Math.abs(value) > 1e6)
    throw new Error(`${label} must be a finite number`);
  return value;
}

function paperPoint(value: unknown, label: string, pages: number): PaperMarkPoint {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  const page = positiveInteger(value.page, `${label} page`);
  if (page > pages) throw new Error(`${label} page is beyond the last page`);
  if (value.mode !== "v" && value.mode !== "h") throw new Error(`${label} mode must be "v" or "h"`);
  return {
    page,
    x: finiteNumber(value.x, `${label} x`),
    y: finiteNumber(value.y, `${label} y`),
    mode: value.mode,
  };
}

/**
 * The optional `paper.web` key: the derived reflow bundle's identity. Same
 * stance as the rest of the paper block — the archive validated fail-closed;
 * this repeats the structural part so corruption is named at build time.
 */
function paperWebEntry(value: unknown, label: string): PaperWebEntry {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  if (!isObject(value.format)) throw new Error(`${label} format must be an object`);
  if (typeof value.format.tool !== "string" || value.format.tool === "")
    throw new Error(`${label} format tool must be a string`);
  if (typeof value.format.rev !== "string" || value.format.rev === "")
    throw new Error(`${label} format rev must be a string`);
  if (typeof value.format.schema !== "string" || !SHA256_HEX.test(value.format.schema))
    throw new Error(`${label} format schema must be a sha256 hex string`);
  if (!isObject(value.bundle)) throw new Error(`${label} bundle must be an object`);
  if (typeof value.bundle.digest !== "string" || !SHA256_HEX.test(value.bundle.digest))
    throw new Error(`${label} bundle digest must be a sha256 hex string`);
  const bytes = positiveInteger(value.bundle.bytes, `${label} bundle bytes`);
  if (value.bundle.registryBlob !== undefined && typeof value.bundle.registryBlob !== "string")
    throw new Error(`${label} bundle registryBlob must be a string`);
  return {
    format: { tool: value.format.tool, rev: value.format.rev, schema: value.format.schema },
    bundle: {
      digest: value.bundle.digest,
      bytes,
      ...(value.bundle.registryBlob === undefined ? {} : { registryBlob: value.bundle.registryBlob }),
    },
  };
}

/**
 * The `paper` key of a stored build output, checked to the shape the viewer
 * relies on. The archive validated it fail-closed before publishing; this
 * repeats the structural part so a corrupt record fails the build here,
 * with the record named, rather than in a browser.
 */
function paperEntry(value: unknown, label: string): PaperEntry {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  for (const key of ["folder", "main", "engine"] as const)
    if (typeof value[key] !== "string") throw new Error(`${label} ${key} must be a string`);
  if (!isObject(value.pdf)) throw new Error(`${label} pdf must be an object`);
  if (typeof value.pdf.digest !== "string" || !SHA256_HEX.test(value.pdf.digest))
    throw new Error(`${label} pdf digest must be a sha256 hex string`);
  const pages = positiveInteger(value.pdf.pages, `${label} pdf pages`);
  if (pages > MAX_PAPER_PAGES) throw new Error(`${label} pdf pages exceeds ${MAX_PAPER_PAGES}`);
  const bytes = positiveInteger(value.pdf.bytes, `${label} pdf bytes`);
  if (value.pdf.registryBlob !== undefined && typeof value.pdf.registryBlob !== "string")
    throw new Error(`${label} pdf registryBlob must be a string`);
  if (!Array.isArray(value.pageSizes) || value.pageSizes.length !== pages)
    throw new Error(`${label} pageSizes must list one [width, height] pair per page`);
  const pageSizes = value.pageSizes.map((size, index): [number, number] => {
    const sizeLabel = `${label} page size ${index + 1}`;
    if (!Array.isArray(size) || size.length !== 2) throw new Error(`${sizeLabel} must be a [width, height] pair`);
    const width = finiteNumber(size[0], `${sizeLabel} width`);
    const height = finiteNumber(size[1], `${sizeLabel} height`);
    if (width <= 0 || height <= 0) throw new Error(`${sizeLabel} must be positive`);
    return [width, height];
  });
  if (!Array.isArray(value.marks) || value.marks.length > MAX_PAPER_MARKS)
    throw new Error(`${label} marks must be an array of at most ${MAX_PAPER_MARKS} entries`);
  const marks = value.marks.map((mark, index): PaperMark => {
    const markLabel = `${label} mark ${index + 1}`;
    if (!isObject(mark)) throw new Error(`${markLabel} must be an object`);
    if (typeof mark.id !== "string" || mark.id.trim() === "") throw new Error(`${markLabel} id must be a string`);
    if (mark.kind !== "concept" && mark.kind !== "proof" && mark.kind !== "submission")
      throw new Error(`${markLabel} kind is invalid`);
    return {
      id: mark.id,
      kind: mark.kind,
      begin: paperPoint(mark.begin, `${markLabel} begin`, pages),
      end: paperPoint(mark.end, `${markLabel} end`, pages),
    };
  });
  return {
    folder: value.folder as string,
    main: value.main as string,
    engine: value.engine as string,
    pdf: {
      digest: value.pdf.digest,
      bytes,
      pages,
      ...(value.pdf.registryBlob === undefined ? {} : { registryBlob: value.pdf.registryBlob }),
    },
    pageSizes,
    marks,
    ...(value.web === undefined ? {} : { web: paperWebEntry(value.web, `${label} web`) }),
  };
}

/** Adapt the stored Archive schema to the renderer's stable public model. */
function rendererOutput(value: unknown, label: string): BuildOutput | undefined {
  if (!isObject(value)) throw new Error(`${label} must contain a JSON object`);
  const inputs = isObject(value.inputs) ? value.inputs : undefined;
  const manifest = value.manifest ?? inputs?.manifest;
  if (manifest === undefined) return undefined;
  const output: Record<string, unknown> = {
    ...value,
    manifest,
    abstract: value.abstract ?? inputs?.abstract,
  };
  if (!isObject(output.manifest)) throw new Error(`${label} manifest must be an object`);
  if (typeof output.abstract !== "string") throw new Error(`${label} abstract must be a string`);
  for (const name of ["requiredByConcepts", "requiredByProofs", "concepts", "proofs"] as const) {
    if (!Array.isArray(output[name])) throw new Error(`${label} ${name} must be an array`);
  }
  if (output.paper !== undefined) output.paper = paperEntry(output.paper, `${label} paper`);
  return output as unknown as BuildOutput;
}

export interface LoadOptions {
  /**
   * The papers cache: `<papersDir>/<digest>.pdf` per compiled paper, filled
   * by `npm run papers:fetch`. Omitted, no PDF is attached and paper pages
   * render without the viewer — the preview policy.
   */
  papersDir?: string;
  /**
   * The web bundles cache: `<bundlesDir>/<digest>.tar` per derived reflow
   * bundle, filled by the same `npm run papers:fetch`. Omitted (previews,
   * `--no-papers`), no bundle is attached and paper pages keep the PDF-only
   * shape — one flag governs both caches.
   */
  bundlesDir?: string;
}

/**
 * Read the checked-out public archive database. The website never mutates
 * this input and deliberately needs no access to server operational state.
 */
export function loadSubmissions(databaseDir: string, options: LoadOptions = {}): SiteSubmission[] {
  const root = path.resolve(databaseDir);
  if (!fs.existsSync(root) || !fs.statSync(root).isDirectory())
    throw new Error(`database directory does not exist: ${root}`);

  return fs.readdirSync(root)
    .filter((id) => fs.existsSync(path.join(root, id, "record.json")))
    .sort()
    .flatMap((id) => {
      const record = readJson<DbRecord>(path.join(root, id, "record.json"));
      if (!record) throw new Error(`missing record for ${id}`);

      // Initialization reserves an archive id and stores only a provenance
      // stub in build-output.json. It is not a website submission yet: do not
      // parse the stub or generate any page for it.
      if (record.state === "init") return [];

      const outputFile = path.join(root, id, "build-output.json");
      const rawOutput = readJson<unknown>(outputFile);
      const output = rawOutput === undefined ? undefined : rendererOutput(rawOutput, outputFile);
      const submission: SiteSubmission = { record, output };
      if (output?.paper && options.papersDir !== undefined) {
        const file = paperCachePath(options.papersDir, output.paper.pdf.digest);
        if (fs.existsSync(file)) submission.paperFile = file;
      }
      if (output?.paper?.web && options.bundlesDir !== undefined) {
        const file = bundleCachePath(options.bundlesDir, output.paper.web.bundle.digest);
        if (fs.existsSync(file)) submission.bundleFile = file;
      }
      return [submission];
    });
}

/** Paper-bearing submissions whose PDF — or whose declared reflow bundle —
 * the loader could not attach. Both are filled by `npm run papers:fetch`. */
export function submissionsMissingPapers(submissions: SiteSubmission[]): SiteSubmission[] {
  return submissions.filter((submission) => {
    if (submission.record.state === "deleted") return false;
    const paper = submission.output?.paper;
    if (!paper) return false;
    return !submission.paperFile || (paper.web !== undefined && !submission.bundleFile);
  });
}
