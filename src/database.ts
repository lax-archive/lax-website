import fs from "node:fs";
import path from "node:path";
import { bundleCachePath } from "./bundles.js";
import { BLOB_REFERENCE, paperCachePath } from "./papers.js";
import { loadReferences } from "./references.js";
import { loadMathlibSources } from "./mathlib-links.js";
import type {
  BuildOutput, CaptureReferences, CertificateEntry, DbRecord, PaperEntry, PaperMark, PaperMarkPoint,
  PaperWebEntry, ProofTelescope, SkippedRecord,
} from "./types.js";
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

const MAX_CHALLENGE_BYTES = 4 * 1024 * 1024;
const MAX_TELESCOPE_HYPOTHESES = 10_000;

// The archive's name grammar, mirrored from lax's contracts.ts
// `LEAN_NAME_PATTERN` (keep the two identical): a name as Lean's escaped
// `Name.toString` prints it when no component needs `«»` — dot-separated
// plain Lean identifiers (`isIdFirst`/`isIdRest`, v4.33.0 through v4.35.0),
// never `_` alone.
const LEAN_LETTER_LIKE =
  "\\u03b1-\\u03ba\\u03bc-\\u03c9" + // lower Greek, but λ
  "\\u0391-\\u039f\\u03a1\\u03a2\\u03a4-\\u03a9" + // upper Greek, but Π and Σ
  "\\u03ca-\\u03fb" + // Coptic
  "\\u1f00-\\u1ffe" + // polytonic Greek
  "\\u2100-\\u214f" + // the letterlike block (ℕ, ℘)
  "\\u{1d49c}-\\u{1d59f}" + // script, double-struck, fraktur Latin
  "\\u00c0-\\u00d6\\u00d8-\\u00f6\\u00f8-\\u00ff" + // Latin-1 letters, but × and ÷
  "\\u0100-\\u017f"; // Latin Extended-A
const LEAN_ID_FIRST = `A-Za-z_${LEAN_LETTER_LIKE}`;
const LEAN_ID_REST = `${LEAN_ID_FIRST}0-9'!?\\u2080-\\u2089\\u2090-\\u209c\\u1d62-\\u1d6a\\u2c7c`;
const LEAN_ID_COMPONENT = `[${LEAN_ID_FIRST}][${LEAN_ID_REST}]*`;
/** A Lean name in the archive's grammar, as every statement, proof, and concept id is one. */
const LEAN_NAME = new RegExp(`^(?!_$)${LEAN_ID_COMPONENT}(?:\\.${LEAN_ID_COMPONENT})*$`, "u");

function stringList(value: unknown, label: string): string[] {
  if (!Array.isArray(value) || value.some((entry) => typeof entry !== "string"))
    throw new Error(`${label} must be an array of strings`);
  return value as string[];
}

/** A spec-2 proof's telescope, checked to the shape the derivation and the
 * proof cards rely on: statement constants in binder order, each with its
 * level instantiation, and the concluded constant. */
function proofTelescope(value: unknown, label: string): ProofTelescope {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  if (!Array.isArray(value.hypotheses) || value.hypotheses.length > MAX_TELESCOPE_HYPOTHESES)
    throw new Error(`${label} hypotheses must be an array of at most ${MAX_TELESCOPE_HYPOTHESES} entries`);
  const hypotheses = value.hypotheses.map((hypothesis, index): ProofTelescope["hypotheses"][number] => {
    const entry = `${label} hypothesis ${index + 1}`;
    if (!isObject(hypothesis)) throw new Error(`${entry} must be an object`);
    if (typeof hypothesis.statement !== "string" || !LEAN_NAME.test(hypothesis.statement))
      throw new Error(`${entry} statement must be a Lean name`);
    return { statement: hypothesis.statement, levels: stringList(hypothesis.levels, `${entry} levels`) };
  });
  if (!isObject(value.conclusion)) throw new Error(`${label} conclusion must be an object`);
  if (typeof value.conclusion.statement !== "string" || !LEAN_NAME.test(value.conclusion.statement))
    throw new Error(`${label} conclusion statement must be a Lean name`);
  return { hypotheses, conclusion: { statement: value.conclusion.statement, levels: stringList(value.conclusion.levels, `${label} conclusion levels`) } };
}

/** `conclusion` and `assumptions` as a telescope defines them: the concluded
 * constant, and the hypothesis constants as a sorted set — the one derivation
 * rule every reader of a spec-2 record shares (`recorded-shape.ts` in `lax`). */
export function derivedEdge(telescope: ProofTelescope): { conclusion: string; assumptions: string[] } {
  return {
    conclusion: telescope.conclusion.statement,
    assumptions: [...new Set(telescope.hypotheses.map((hypothesis) => hypothesis.statement))].sort(),
  };
}

/** A spec-2 capture's `references` layer, checked to what the download relies
 * on: a sha256 digest, a size, and — when published — a blob address that
 * carries exactly that digest. */
function captureReferences(value: unknown, label: string): CaptureReferences {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  if (typeof value.digest !== "string" || !SHA256_HEX.test(value.digest))
    throw new Error(`${label} digest must be a sha256 hex string`);
  const bytes = positiveInteger(value.bytes, `${label} bytes`);
  if (value.registryBlob !== undefined) {
    if (typeof value.registryBlob !== "string") throw new Error(`${label} registryBlob must be a string`);
    const address = BLOB_REFERENCE.exec(value.registryBlob);
    if (address === null || address[2] !== value.digest)
      throw new Error(`${label} registryBlob is not a ghcr address of its digest`);
  }
  return { digest: value.digest, bytes, ...(value.registryBlob === undefined ? {} : { registryBlob: value.registryBlob }) };
}

/** The `certificate` key of a spec-2 record, checked to the shape the
 * certified mark and the Challenge section rely on. The archive's trusted
 * parser held the Challenge to its regeneration from the telescopes before
 * publishing; this repeats the structural part so corruption is named here. */
function certificateEntry(value: unknown, label: string): CertificateEntry {
  if (!isObject(value)) throw new Error(`${label} must be an object`);
  const kernels = stringList(value.kernels, `${label} kernels`);
  if (kernels.length === 0 || kernels.some((kernel) => !/^[a-z0-9-]+$/u.test(kernel)))
    throw new Error(`${label} kernels must name at least one kernel`);
  if (!isObject(value.bundle)) throw new Error(`${label} bundle must be an object`);
  const formatVersion = positiveInteger(value.bundle.formatVersion, `${label} bundle formatVersion`);
  if (typeof value.bundle.digest !== "string" || !SHA256_HEX.test(value.bundle.digest))
    throw new Error(`${label} bundle digest must be a sha256 hex string`);
  if (value.bundle.registryBlob !== undefined) {
    if (typeof value.bundle.registryBlob !== "string") throw new Error(`${label} bundle registryBlob must be a string`);
    const address = BLOB_REFERENCE.exec(value.bundle.registryBlob);
    if (address === null || address[2] !== value.bundle.digest)
      throw new Error(`${label} bundle registryBlob is not a ghcr address of its digest`);
  }
  if (typeof value.challengeExportSha256 !== "string" || !SHA256_HEX.test(value.challengeExportSha256))
    throw new Error(`${label} challengeExportSha256 must be a sha256 hex string`);
  if (typeof value.solutionExportSha256 !== "string" || !SHA256_HEX.test(value.solutionExportSha256))
    throw new Error(`${label} solutionExportSha256 must be a sha256 hex string`);
  if (typeof value.challenge !== "string" || value.challenge === "" || Buffer.byteLength(value.challenge) > MAX_CHALLENGE_BYTES)
    throw new Error(`${label} challenge must be the Challenge.lean source, at most ${MAX_CHALLENGE_BYTES} bytes`);
  return {
    kernels,
    bundle: {
      formatVersion,
      digest: value.bundle.digest,
      ...(value.bundle.registryBlob === undefined ? {} : { registryBlob: value.bundle.registryBlob }),
    },
    challengeExportSha256: value.challengeExportSha256,
    solutionExportSha256: value.solutionExportSha256,
    challenge: value.challenge,
  };
}

/**
 * The spec-2 record shape, expanded to the renderer's one in-memory model.
 * A spec-2 record stores no field a reader derives from something else in
 * it (`recorded-shape.ts` in `lax`): the manifest has no `id` (the record's
 * own id is it), a proof stores its telescope and no `conclusion` or
 * `assumptions`, the capture lists no files and no pins, and the paper block
 * repeats nothing of the manifest's `paper`. Filling those in here lets the
 * site model, the proof network, and every page run on both specs unchanged.
 * The spec-1 branch of `rendererOutput` is deliberately untouched.
 */
function expandSpec2(value: Record<string, unknown>, manifest: Record<string, unknown>, id: string, label: string): Record<string, unknown> {
  if (manifest.id !== undefined && manifest.id !== id)
    throw new Error(`${label} manifest names ${JSON.stringify(manifest.id)}, not ${id}`);
  if (!Array.isArray(value.proofs)) throw new Error(`${label} proofs must be an array`);
  const proofs = value.proofs.map((proof, index) => {
    const entry = `${label} proof ${index + 1}`;
    if (!isObject(proof)) throw new Error(`${entry} must be an object`);
    const telescope = proofTelescope(proof.telescope, `${entry} telescope`);
    if (proof.pending !== undefined && proof.pending !== true) throw new Error(`${entry} pending must be true when present`);
    return { ...proof, levelParams: stringList(proof.levelParams ?? [], `${entry} levelParams`), telescope, ...derivedEdge(telescope) };
  });
  const capture = isObject(value.capture)
    ? { ...value.capture, ...(value.capture.references === undefined ? {} : { references: captureReferences(value.capture.references, `${label} capture references`) }) }
    : value.capture;
  let paper = value.paper;
  if (paper !== undefined) {
    if (!isObject(paper)) throw new Error(`${label} paper must be an object`);
    const declared = manifest.paper;
    if (!isObject(declared)) throw new Error(`${label} manifest declares no paper for the paper block`);
    paper = { folder: declared.folder, main: declared.main, engine: declared.engine, ...paper };
  }
  // The certificate judges the complete proofs only: a record whose proofs
  // are all pending edges (lax decision 12) has none.
  const complete = value.proofs.some((proof) => isObject(proof) && proof.pending !== true);
  if (value.certificate !== undefined && !complete)
    throw new Error(`${label} certificate is present on a record without a complete proof`);
  if (value.certificate === undefined && complete)
    throw new Error(`${label} certificate is missing on a record with a complete proof`);
  return {
    ...value,
    inputs: { ...(isObject(value.inputs) ? value.inputs : {}), manifest: { id, ...manifest } },
    proofs,
    ...(capture === undefined ? {} : { capture }),
    ...(paper === undefined ? {} : { paper }),
    ...(value.certificate === undefined ? {} : { certificate: certificateEntry(value.certificate, `${label} certificate`) }),
  };
}

/** Adapt the stored Archive schema to the renderer's stable public model.
 * Keyed on the record's content spec, `inputs.manifest.specVersion`: a spec-1
 * record passes through as it always has, a spec-2 record is expanded first. */
export function rendererOutput(raw: unknown, label: string, id?: string): BuildOutput | undefined {
  if (!isObject(raw)) throw new Error(`${label} must contain a JSON object`);
  const rawInputs = isObject(raw.inputs) ? raw.inputs : undefined;
  const storedManifest = raw.manifest ?? rawInputs?.manifest;
  const value = isObject(storedManifest) && storedManifest.specVersion === "2"
    ? expandSpec2(raw, storedManifest, id ?? (typeof raw.id === "string" ? raw.id : ""), label)
    : raw;
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
  /** Verified .ilean cache; omitted for local callers without captures. */
  referencesDir?: string;
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
  /**
   * Where a record the loader leaves out is reported: one that does not
   * parse, or whose build output fails the shape checks above. Defaults to
   * a console warning, so no caller can skip a record silently.
   */
  onSkip?: (skipped: SkippedRecord) => void;
}

/**
 * Read the checked-out public archive database. The website never mutates
 * this input and deliberately needs no access to server operational state.
 *
 * Each record is a boundary of its own: a malformed one is skipped and
 * reported through `onSkip`, and the rest of the archive still builds. The
 * archive validated every record fail-closed before publishing, so a skip
 * here is corruption to be fixed in the database, never something to hide —
 * but also never a reason to stop publishing every other record.
 */
export function loadSubmissions(databaseDir: string, options: LoadOptions = {}): SiteSubmission[] {
  const root = path.resolve(databaseDir);
  if (!fs.existsSync(root) || !fs.statSync(root).isDirectory())
    throw new Error(`database directory does not exist: ${root}`);
  const skip = options.onSkip ?? ((skipped: SkippedRecord) => console.warn(`skipping ${skipped.id}: ${skipped.reason}`));

  return fs.readdirSync(root)
    .filter((id) => fs.existsSync(path.join(root, id, "record.json")))
    .sort()
    .flatMap((id) => {
      try {
        return loadSubmission(root, id, options);
      } catch (error) {
        skip({ id, reason: error instanceof Error ? error.message : String(error) });
        return [];
      }
    });
}

function loadSubmission(root: string, id: string, options: LoadOptions): SiteSubmission[] {
  const recordFile = path.join(root, id, "record.json");
  const record = readJson<unknown>(recordFile);
  if (!isObject(record)) throw new Error(`${recordFile} must contain a JSON object`);
  if (record.id !== id) throw new Error(`${recordFile} names ${JSON.stringify(record.id)}, not ${id}`);
  if (!["init", "draft", "registered", "deleted"].includes(record.state as string))
    throw new Error(`${recordFile} has an unknown state ${JSON.stringify(record.state)}`);
  if (typeof record.createdAt !== "string") throw new Error(`${recordFile} createdAt must be a string`);

  // Initialization reserves an archive id and stores only a provenance
  // stub in build-output.json. It is not a website submission yet: do not
  // parse the stub or generate any page for it.
  if (record.state === "init") return [];

  const outputFile = path.join(root, id, "build-output.json");
  const rawOutput = readJson<unknown>(outputFile);
  const output = rawOutput === undefined ? undefined : rendererOutput(rawOutput, outputFile, id);
  const submission: SiteSubmission = { record: record as unknown as DbRecord, output };
  if (options.referencesDir !== undefined) {
    submission.sourceReferences = loadReferences(submission, options.referencesDir);
    submission.mathlibSources = loadMathlibSources(submission, options.referencesDir);
  }
  if (output?.paper && options.papersDir !== undefined) {
    const file = paperCachePath(options.papersDir, output.paper.pdf.digest);
    if (fs.existsSync(file)) submission.paperFile = file;
  }
  if (output?.paper?.web && options.bundlesDir !== undefined) {
    const file = bundleCachePath(options.bundlesDir, output.paper.web.bundle.digest);
    if (fs.existsSync(file)) submission.bundleFile = file;
  }
  return [submission];
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
