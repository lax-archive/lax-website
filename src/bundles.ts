// The web bundles cache: one `<digest>.tar` per derived reflow bundle the
// database references (`paper.web` in a record's build output), filled by the
// same `papers:fetch` pass that fills the PDF cache and read back by the site
// build. The tar is the archive's sealed ReflowTeX bundle — `index.json`,
// `blocks/*.pb`, `fonts/*.otf|ttf`, `schema/latex.proto` — and although its
// bytes are digest-verified on the way in, everything here treats it as an
// attacker-shaped input: a bounded ustar reader with an exact path allowlist,
// entry and size caps, files only, no links, no traversal, fail closed.

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { BLOB_REFERENCE, downloadBlob, MAX_PAPER_BYTES } from "./papers.js";
import type { SiteSubmission } from "./sitegen/model.js";

/** The bundle rides the paper layer's 25 MiB cap. */
export const MAX_BUNDLE_BYTES = MAX_PAPER_BYTES;
/** Sealed bundles hold an index, a schema, a handful of blocks, and the
 * fonts one document uses; hundreds of entries is not one of ours. */
export const MAX_BUNDLE_ENTRIES = 512;
/** No single member may approach the whole-bundle cap on its own. */
export const MAX_BUNDLE_FILE_BYTES = 20 * 1024 * 1024;

/** Exactly the names the archive seals — anything else fails the extract. */
const BUNDLE_NAME = /^(?:index\.json|schema\/latex\.proto|blocks\/\d{3}\.pb|fonts\/[A-Za-z0-9][A-Za-z0-9._-]{0,199}\.(?:otf|ttf))$/u;

export function bundleCachePath(bundlesDir: string, digest: string): string {
  if (!/^[0-9a-f]{64}$/u.test(digest)) throw new Error(`bundle digest is not sha256 hex: ${digest}`);
  return path.join(path.resolve(bundlesDir), `${digest}.tar`);
}

export interface BundleReference {
  submissionId: string;
  digest: string;
  registryBlob: string;
}

/** Every distinct web bundle the listed submissions reference, by digest. */
export function bundleReferences(submissions: SiteSubmission[]): BundleReference[] {
  const byDigest = new Map<string, BundleReference>();
  for (const submission of submissions) {
    if (submission.record.state === "deleted") continue;
    const web = submission.output?.paper?.web;
    if (!web) continue;
    if (web.bundle.registryBlob === undefined)
      throw new Error(`${submission.record.id} declares a paper web bundle without a registry blob`);
    const match = BLOB_REFERENCE.exec(web.bundle.registryBlob);
    if (match === null || match[2] !== web.bundle.digest)
      throw new Error(`${submission.record.id} paper web registryBlob is not a ghcr address of its digest`);
    if (!byDigest.has(web.bundle.digest))
      byDigest.set(web.bundle.digest, { submissionId: submission.record.id, digest: web.bundle.digest, registryBlob: web.bundle.registryBlob });
  }
  return [...byDigest.values()].sort((a, b) => a.digest.localeCompare(b.digest));
}

export interface FetchBundleOptions {
  fetch?: typeof fetch;
  log?: (line: string) => void;
}

/** Download every referenced bundle the cache lacks. Returns the digests fetched. */
export async function fetchBundles(
  submissions: SiteSubmission[],
  bundlesDir: string,
  options: FetchBundleOptions = {},
): Promise<string[]> {
  const doFetch = options.fetch ?? fetch;
  const log = options.log ?? (() => {});
  fs.mkdirSync(path.resolve(bundlesDir), { recursive: true });
  const fetched: string[] = [];
  for (const reference of bundleReferences(submissions)) {
    const file = bundleCachePath(bundlesDir, reference.digest);
    if (fs.existsSync(file)) continue;
    log(`fetching web bundle of ${reference.submissionId} (${reference.digest.slice(0, 12)})`);
    const bytes = await downloadBlob(reference.registryBlob, doFetch);
    const digest = createHash("sha256").update(bytes).digest("hex");
    if (digest !== reference.digest)
      throw new Error(`web bundle of ${reference.submissionId} downloaded with digest ${digest}, expected ${reference.digest}`);
    if (bytes.subarray(257, 262).toString("latin1") !== "ustar")
      throw new Error(`web bundle of ${reference.submissionId} is not a ustar archive`);
    const temporary = `${file}.${process.pid}.part`;
    fs.writeFileSync(temporary, bytes, { mode: 0o644 });
    fs.renameSync(temporary, file);
    fetched.push(reference.digest);
  }
  return fetched;
}

// ---- the bounded extractor ----

function parseOctal(field: Buffer, label: string): number {
  const text = field.toString("latin1").replace(/\0.*$/su, "").trim();
  if (field[0] !== undefined && (field[0] & 0x80) !== 0)
    throw new Error(`bundle tar uses a base-256 ${label}; ours are plain ustar`);
  if (text === "") return 0;
  if (!/^[0-7]+$/u.test(text)) throw new Error(`bundle tar has a malformed ${label}`);
  return Number.parseInt(text, 8);
}

/**
 * Extract the sealed bundle tar: plain ustar, regular files only, every name
 * on the exact allowlist, header checksums verified, entry/file/total caps,
 * no duplicates, nothing but zero padding after the terminator. Anything
 * else throws — the caller names the record.
 */
export function extractBundleTar(bytes: Buffer): Map<string, Buffer> {
  if (bytes.length > MAX_BUNDLE_BYTES) throw new Error(`bundle exceeds ${MAX_BUNDLE_BYTES} bytes`);
  if (bytes.length % 512 !== 0) throw new Error("bundle tar is not block-aligned");
  const files = new Map<string, Buffer>();
  let offset = 0;
  let total = 0;
  while (offset < bytes.length) {
    const header = bytes.subarray(offset, offset + 512);
    if (header.length < 512) throw new Error("bundle tar is truncated");
    if (header.every((byte) => byte === 0)) {
      // The terminator: nothing but zero padding may follow.
      if (!bytes.subarray(offset).every((byte) => byte === 0))
        throw new Error("bundle tar carries data after its terminator");
      return files;
    }
    // The checksum is computed with its own field read as spaces.
    const stored = parseOctal(header.subarray(148, 156), "checksum");
    let sum = 0;
    for (let i = 0; i < 512; i += 1) sum += i >= 148 && i < 156 ? 0x20 : header[i]!;
    if (sum !== stored) throw new Error("bundle tar entry fails its header checksum");
    if (header.subarray(257, 262).toString("latin1") !== "ustar")
      throw new Error("bundle tar entry is not ustar");
    if (!header.subarray(345, 500).every((byte) => byte === 0))
      throw new Error("bundle tar entry uses the ustar prefix field; sealed bundles never do");
    const typeflag = header[156]!;
    if (typeflag !== 0x30 && typeflag !== 0)
      throw new Error(`bundle tar entry is not a regular file (typeflag ${String.fromCharCode(typeflag)})`);
    const name = header.subarray(0, 100).toString("latin1").replace(/\0.*$/su, "");
    if (!BUNDLE_NAME.test(name)) throw new Error(`bundle tar entry has a disallowed name: ${name}`);
    if (files.has(name)) throw new Error(`bundle tar repeats ${name}`);
    const size = parseOctal(header.subarray(124, 136), "size");
    if (size > MAX_BUNDLE_FILE_BYTES) throw new Error(`bundle member ${name} exceeds ${MAX_BUNDLE_FILE_BYTES} bytes`);
    total += size;
    if (total > MAX_BUNDLE_BYTES) throw new Error(`bundle members exceed ${MAX_BUNDLE_BYTES} bytes together`);
    const dataStart = offset + 512;
    const dataEnd = dataStart + size;
    if (dataEnd > bytes.length) throw new Error(`bundle tar is truncated inside ${name}`);
    files.set(name, Buffer.from(bytes.subarray(dataStart, dataEnd)));
    if (files.size > MAX_BUNDLE_ENTRIES) throw new Error(`bundle tar exceeds ${MAX_BUNDLE_ENTRIES} entries`);
    offset = dataStart + Math.ceil(size / 512) * 512;
  }
  throw new Error("bundle tar ends without a terminator");
}

// ---- the bundle's own index ----

export interface BundleIndex {
  formatVersion: number;
  tool: string;
  rev: string;
  schema: string;
  /** Ordered block member names, e.g. `blocks/000.pb`. */
  blocks: string[];
  /** Original font name (as the blocks reference it) → member name. */
  fonts: Record<string, string>;
}

export interface PaperBundle {
  index: BundleIndex;
  files: Map<string, Buffer>;
}

function isObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

/**
 * Extract and cross-check a bundle: the index must exist and describe the
 * tar exactly — every block and font it names present, every member it does
 * not name absent, and the embedded schema hashing to the index's own
 * `schema` value. Fail closed; the schema *gate* (whether this viewer
 * supports that schema) is the caller's separate, graceful decision.
 */
export function readPaperBundle(bytes: Buffer): PaperBundle {
  const files = extractBundleTar(bytes);
  const indexBytes = files.get("index.json");
  if (!indexBytes) throw new Error("bundle has no index.json");
  let parsed: unknown;
  try {
    parsed = JSON.parse(indexBytes.toString("utf8"));
  } catch {
    throw new Error("bundle index.json is not valid JSON");
  }
  if (!isObject(parsed)) throw new Error("bundle index.json must be an object");
  if (typeof parsed.formatVersion !== "number" || !Number.isInteger(parsed.formatVersion))
    throw new Error("bundle index formatVersion must be an integer");
  if (typeof parsed.tool !== "string" || parsed.tool === "") throw new Error("bundle index tool must be a string");
  if (typeof parsed.rev !== "string" || parsed.rev === "") throw new Error("bundle index rev must be a string");
  if (typeof parsed.schema !== "string" || !/^[0-9a-f]{64}$/u.test(parsed.schema))
    throw new Error("bundle index schema must be a sha256 hex string");
  if (!Array.isArray(parsed.blocks) || parsed.blocks.length === 0)
    throw new Error("bundle index blocks must be a non-empty array");
  const blocks = parsed.blocks.map((name) => {
    if (typeof name !== "string" || !/^blocks\/\d{3}\.pb$/u.test(name))
      throw new Error(`bundle index names an invalid block: ${String(name)}`);
    if (!files.has(name)) throw new Error(`bundle index names a missing block: ${name}`);
    return name;
  });
  if (new Set(blocks).size !== blocks.length) throw new Error("bundle index repeats a block");
  if (!isObject(parsed.fonts)) throw new Error("bundle index fonts must be an object");
  const fonts: Record<string, string> = {};
  for (const [original, member] of Object.entries(parsed.fonts)) {
    if (original === "" ) throw new Error("bundle index maps an empty font name");
    if (typeof member !== "string" || !/^fonts\//u.test(member))
      throw new Error(`bundle index maps font ${original} outside fonts/`);
    if (!files.has(member)) throw new Error(`bundle index names a missing font: ${member}`);
    fonts[original] = member;
  }
  const schemaBytes = files.get("schema/latex.proto");
  if (!schemaBytes) throw new Error("bundle has no schema/latex.proto");
  const schemaDigest = createHash("sha256").update(schemaBytes).digest("hex");
  if (schemaDigest !== parsed.schema)
    throw new Error(`bundle schema/latex.proto hashes to ${schemaDigest}, index says ${parsed.schema}`);
  const referenced = new Set(["index.json", "schema/latex.proto", ...blocks, ...Object.values(fonts)]);
  for (const name of files.keys())
    if (!referenced.has(name)) throw new Error(`bundle carries a member its index does not reference: ${name}`);
  return {
    index: { formatVersion: parsed.formatVersion, tool: parsed.tool, rev: parsed.rev, schema: parsed.schema, blocks, fonts },
    files,
  };
}
