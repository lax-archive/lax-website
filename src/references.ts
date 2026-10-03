/** Build-time cache of the compiler's reference maps from sealed captures.
 * Captures are deterministic, uncompressed ustar. Two records shapes, two
 * paths to the same `.ilean` bytes:
 *
 * - a spec-1 record lists the capture's files, so just the .ilean members
 *   are read as bounded byte ranges of the capture tar, each verified
 *   against its header and recorded SHA-256;
 * - a spec-2 record lists no files but names a `references` layer beside
 *   the capture — the concept sources and their .ilean files as one small
 *   tar — which is downloaded whole and verified by its digest before any
 *   member is read (`captureReferencesLayer`).
 *
 * Neither path extracts a tar to disk or downloads the submission's proof
 * artifacts. */
import { createHash, randomUUID } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { MAX_REFERENCE_BYTES, parseLeanReferences, type LeanReferences } from "./lean-references.js";
import { BLOB_REFERENCE, downloadBlob, type FetchOptions } from "./papers.js";
import type { SiteSubmission } from "./sitegen/model.js";
import type { CaptureEntry, CaptureFile, CaptureReferences, ConceptEntry } from "./types.js";

const SHA256 = /^[0-9a-f]{64}$/u;
const MAX_CAPTURE_BYTES = 2 * 1024 ** 3;
const MAX_CAPTURE_FILES = 100_000;
/** The archive's own cap on a `references` layer (`capture-store.ts`). */
const MAX_REFERENCES_LAYER_BYTES = 64 * 1024 * 1024;
/** `tar`'s default record size: a sealed layer is a whole number of records. */
const TAR_RECORD = 10_240;
const sha256 = (bytes: string | Buffer): string => createHash("sha256").update(bytes).digest("hex");

export function referenceCachePath(directory: string, digest: string): string {
  if (!SHA256.test(digest)) throw new Error("reference digest is not sha256 hex");
  return path.join(path.resolve(directory), `${digest}.ilean`);
}

/** Where a spec-2 record's verified `references` layer is cached, whole, by
 * its own digest: `<digest>.references.tar` beside the spec-1 `.ilean` files. */
export function referenceLayerPath(directory: string, digest: string): string {
  if (!SHA256.test(digest)) throw new Error("reference layer digest is not sha256 hex");
  return path.join(path.resolve(directory), `${digest}.references.tar`);
}

/** Validate the manifest before using its sizes to address the sealed tar. */
function captureFiles(capture: CaptureEntry): Map<string, CaptureFile> {
  const address = BLOB_REFERENCE.exec(capture.registryBlob ?? "");
  if (capture.formatVersion !== 1 || !address || address[2] !== capture.digest ||
    !Array.isArray(capture.files) || capture.files.length > MAX_CAPTURE_FILES)
    throw new Error("unsupported or invalid reference capture manifest");
  const files = new Map<string, CaptureFile>();
  let total = 0;
  for (const file of capture.files) {
    if (!file || typeof file.path !== "string" || Buffer.byteLength(file.path) > 255 ||
      /[\\\x00-\x1f\x7f]/u.test(file.path) || file.path.split("/").some((part) => !part || part === "." || part === "..") ||
      file.path.split("/").length > 64 || files.has(file.path) ||
      !Number.isSafeInteger(file.bytes) || file.bytes < 0 || typeof file.sha256 !== "string" || !SHA256.test(file.sha256))
      throw new Error("invalid or duplicate reference capture member");
    total += file.bytes;
    if (total > MAX_CAPTURE_BYTES) throw new Error("reference capture exceeds size limit");
    files.set(file.path, file);
  }
  return files;
}

/** A concept's two members of a capture or of its `references` layer: the
 * source (`concepts/package/<module>.lean`) and the metadata
 * (`concepts/lib/<module>.ilean`). */
function memberPaths(concept: ConceptEntry): { source: string; metadata: string } {
  if (!concept.path.startsWith("concepts/") || !concept.path.endsWith(".lean"))
    throw new Error(`${concept.id}: invalid captured concept path`);
  const relative = concept.path.slice("concepts/".length);
  return { source: `concepts/package/${relative}`, metadata: `concepts/lib/${relative.slice(0, -5)}.ilean` };
}

/** A spec-2 record's `references` layer, when the record is one the reader
 * fetches for: a published layer address on a record with concepts. A record
 * whose capture carries neither a file list nor a layer (a local build, or a
 * record handed over with its address withheld) has nothing to fetch. */
function referencesLayer(submission: SiteSubmission): CaptureReferences | undefined {
  const output = submission.output;
  const references = output?.capture?.references;
  if (submission.record.state === "deleted" || !output?.concepts.length || output.manifest.specVersion !== "2" ||
    references === undefined || references.registryBlob === undefined) return undefined;
  if (!SHA256.test(references.digest) || BLOB_REFERENCE.exec(references.registryBlob)?.[2] !== references.digest ||
    !Number.isSafeInteger(references.bytes) || references.bytes <= 0 || references.bytes > MAX_REFERENCES_LAYER_BYTES ||
    references.bytes % TAR_RECORD !== 0)
    throw new Error(`${submission.record.id}: unsupported or invalid references layer`);
  return references;
}

interface ReferenceJob { concept: ConceptEntry; file: CaptureFile }
function jobs(submission: SiteSubmission): { capture: CaptureEntry; files: Map<string, CaptureFile>; wanted: ReferenceJob[] } | undefined {
  const output = submission.output;
  const capture = output?.capture;
  if (submission.record.state === "deleted" || !output?.concepts.length || !capture ||
    output.manifest.specVersion === "2" ||
    (capture.registryBlob === undefined && capture.files === undefined)) return undefined;
  const files = captureFiles(capture);
  const wanted = output.concepts.map((concept) => {
    if (!concept.path.startsWith("concepts/") || !concept.path.endsWith(".lean"))
      throw new Error(`${concept.id}: invalid captured concept path`);
    const relative = concept.path.slice("concepts/".length);
    const source = files.get(`concepts/package/${relative}`);
    const file = files.get(`concepts/lib/${relative.slice(0, -5)}.ilean`);
    if (!source || sha256(concept.sourceText) !== source.sha256 || Buffer.byteLength(concept.sourceText) !== source.bytes)
      throw new Error(`${concept.id}: reference capture does not match displayed source`);
    if (!file || file.bytes > MAX_REFERENCE_BYTES || !file.bytes)
      throw new Error(`${concept.id}: reference capture lacks a supported .ilean member`);
    return { concept, file };
  });
  return { capture, files, wanted };
}

function verified(bytes: Buffer, file: CaptureFile): Buffer {
  if (bytes.length !== file.bytes || sha256(bytes) !== file.sha256)
    throw new Error(`Lean reference digest mismatch for ${file.path}`);
  return bytes;
}

function cached(directory: string, file: CaptureFile): Buffer | undefined {
  const location = referenceCachePath(directory, file.sha256);
  if (!fs.existsSync(location)) return undefined;
  if (fs.statSync(location).size !== file.bytes) throw new Error(`Lean reference cache size mismatch for ${file.path}`);
  return verified(fs.readFileSync(location), file);
}

/** Attach only verified metadata. Missing or stale data fails an archive
 * build, rather than silently dropping links or guessing their targets. */
export function loadReferences(submission: SiteSubmission, directory: string): Map<string, LeanReferences> | undefined {
  const layer = referencesLayer(submission);
  if (layer) return loadReferencesFromLayer(submission, layer, directory);
  const job = jobs(submission);
  if (!job) return undefined;
  const result = new Map<string, LeanReferences>();
  for (const { concept, file } of job.wanted) {
    const bytes = cached(directory, file);
    if (!bytes) throw new Error(`${concept.id}: references cache is missing ${file.sha256}; run \`npm run references:fetch\``);
    result.set(concept.id, parseLeanReferences(bytes.toString("utf8"), concept.id, concept.sourceText));
  }
  return result;
}

/** Mirror capture format 1's `tar --sort=name --format=ustar -C capture .`.
 * Siblings, not flattened paths, are sorted by raw UTF-8 bytes. Every range
 * is still checked against its header and digest, so layout drift fails. */
export function captureOffsets(files: Map<string, CaptureFile>): Map<string, number> {
  const directories = new Set([""]);
  for (const name of files.keys()) {
    const parts = name.split("/");
    for (let i = 1; i < parts.length; i++) {
      directories.add(parts.slice(0, i).join("/"));
      if (directories.size > MAX_CAPTURE_FILES) throw new Error("too many reference capture directories");
    }
  }
  for (const dir of directories) if (files.has(dir)) throw new Error("reference capture file/directory collision");
  const children = new Map<string, string[]>();
  for (const name of [...files.keys(), ...directories]) {
    if (!name) continue;
    const slash = name.lastIndexOf("/");
    const parent = slash < 0 ? "" : name.slice(0, slash);
    const siblings = children.get(parent) ?? [];
    siblings.push(name);
    children.set(parent, siblings);
  }
  const offsets = new Map<string, number>();
  let offset = 0;
  const walk = (name: string) => {
    offsets.set(name, offset);
    offset += 512 + Math.ceil((files.get(name)?.bytes ?? 0) / 512) * 512;
    const siblings = (children.get(name) ?? []).map((child) => ({ name: child, bytes: Buffer.from(child) }));
    siblings.sort((a, b) => Buffer.compare(a.bytes, b.bytes));
    for (const child of siblings) walk(child.name);
  };
  walk("");
  return offsets;
}

function member(bytes: Buffer, file: CaptureFile): Buffer {
  const header = bytes.subarray(0, 512);
  const string = (start: number, length: number): string => header.subarray(start, start + length).toString("utf8").replace(/\0.*$/su, "");
  const octal = (start: number, length: number): number => {
    const text = string(start, length).trim();
    if (!/^[0-7]+$/u.test(text)) throw new Error("invalid reference tar number");
    return parseInt(text, 8);
  };
  let checksum = 0;
  for (let i = 0; i < header.length; i++) checksum += i >= 148 && i < 156 ? 32 : header[i]!;
  const prefix = string(345, 155);
  const name = (prefix ? `${prefix}/` : "") + string(0, 100);
  if (header.length !== 512 || checksum !== octal(148, 8) || string(257, 6) !== "ustar" ||
    (header[156] !== 0 && header[156] !== 48) || name !== `./${file.path}` || octal(124, 12) !== file.bytes)
    throw new Error(`unexpected reference tar header for ${file.path}`);
  return verified(bytes.subarray(512), file);
}

/** At most 2 MiB per group (8 MiB for one large member), joining only gaps
 * up to 64 KiB. Keep traffic proportional to reference data, not proof size. */
export async function fetchReferences(submissions: SiteSubmission[], directory: string, options: FetchOptions = {}): Promise<string[]> {
  fs.mkdirSync(directory, { recursive: true });
  const fetched: string[] = [];
  for (const submission of submissions) {
    const layer = referencesLayer(submission);
    if (layer) {
      if (cachedLayer(directory, layer) === undefined) {
        options.log?.(`fetching the references layer of ${submission.record.id} (${layer.digest.slice(0, 12)})`);
        const bytes = await downloadBlob(layer.registryBlob!, options.fetch ?? fetch);
        const members = verifiedLayer(bytes, layer, submission.record.id);
        layerReferences(submission, members);
        const destination = referenceLayerPath(directory, layer.digest);
        const temporary = `${destination}.${randomUUID()}.part`;
        try {
          fs.writeFileSync(temporary, bytes, { mode: 0o644, flag: "wx" });
          fs.renameSync(temporary, destination);
        } finally { fs.rmSync(temporary, { force: true }); }
        fetched.push(layer.digest);
      }
      continue;
    }
    const job = jobs(submission);
    if (!job) continue;
    const missing = job.wanted.filter(({ file }) => !cached(directory, file));
    if (!missing.length) continue;
    options.log?.(`fetching Lean references of ${submission.record.id} (${missing.length} modules)`);
    const offsets = captureOffsets(job.files);
    const ranges = missing.map((entry) => ({ ...entry, start: offsets.get(entry.file.path)! }))
      .sort((a, b) => a.start - b.start);
    for (let i = 0; i < ranges.length;) {
      const first = ranges[i]!;
      let end = first.start + 512 + first.file.bytes - 1;
      const group = [first];
      i++;
      while (i < ranges.length) {
        const next = ranges[i]!;
        const nextEnd = next.start + 512 + next.file.bytes - 1;
        if (next.start - end > 64 * 1024 || nextEnd - first.start >= 2 * 1024 * 1024) break;
        group.push(next); end = nextEnd; i++;
      }
      const bytes = await downloadBlob(job.capture.registryBlob!, options.fetch ?? fetch, { start: first.start, end });
      for (const entry of group) {
        const start = entry.start - first.start;
        const contents = member(bytes.subarray(start, start + 512 + entry.file.bytes), entry.file);
        parseLeanReferences(contents.toString("utf8"), entry.concept.id, entry.concept.sourceText);
        const destination = referenceCachePath(directory, entry.file.sha256);
        const temporary = `${destination}.${randomUUID()}.part`;
        try {
          fs.writeFileSync(temporary, contents, { mode: 0o644, flag: "wx" });
          fs.renameSync(temporary, destination);
        } finally { fs.rmSync(temporary, { force: true }); }
        fetched.push(entry.file.sha256);
      }
    }
  }
  return fetched;
}

// ---- the spec-2 `references` layer ----

/** The members of a verified layer, by path without the leading `./`. */
type LayerMembers = Map<string, Buffer>;

/**
 * Hold downloaded or cached bytes to the layer the record names — exact size,
 * exact digest — and read them as the plain ustar the archive sealed: regular
 * files only, names on the layer's allowlist (`./concepts/package/**.lean`,
 * `./concepts/lib/**.ilean`), header checksums verified, nothing but zero
 * blocks after the terminator, the whole a multiple of the 10240-byte record.
 * Anything else throws with the record named; nothing is written anywhere.
 */
export function verifiedLayer(bytes: Buffer, layer: CaptureReferences, recordId: string): LayerMembers {
  if (bytes.length !== layer.bytes || sha256(bytes) !== layer.digest)
    throw new Error(`${recordId}: references layer does not match its recorded digest`);
  if (bytes.length % TAR_RECORD !== 0) throw new Error(`${recordId}: references layer is not record-aligned`);
  const members: LayerMembers = new Map();
  let offset = 0;
  for (;;) {
    const header = bytes.subarray(offset, offset + 512);
    if (header.length < 512) throw new Error(`${recordId}: references layer is truncated`);
    if (header.every((byte) => byte === 0)) {
      if (!bytes.subarray(offset).every((byte) => byte === 0))
        throw new Error(`${recordId}: references layer carries data after its terminator`);
      return members;
    }
    const string = (start: number, length: number): string => header.subarray(start, start + length).toString("utf8").replace(/\0.*$/su, "");
    const octal = (start: number, length: number): number => {
      const text = string(start, length).trim();
      if (!/^[0-7]+$/u.test(text)) throw new Error(`${recordId}: references layer has a malformed tar number`);
      return parseInt(text, 8);
    };
    let checksum = 0;
    for (let i = 0; i < 512; i++) checksum += i >= 148 && i < 156 ? 32 : header[i]!;
    if (checksum !== octal(148, 8) || string(257, 6) !== "ustar")
      throw new Error(`${recordId}: references layer member fails its ustar header`);
    if (header[156] !== 0 && header[156] !== 48)
      throw new Error(`${recordId}: references layer member is not a regular file`);
    const prefix = string(345, 155);
    const name = (prefix ? `${prefix}/` : "") + string(0, 100);
    if (!name.startsWith("./") || !/^\.\/concepts\/(?:package\/[^\0]+\.lean|lib\/[^\0]+\.ilean)$/u.test(name) ||
      name.slice(2).split("/").some((part) => !part || part === "." || part === ".."))
      throw new Error(`${recordId}: references layer member has a disallowed name`);
    const member = name.slice(2);
    if (members.has(member)) throw new Error(`${recordId}: references layer repeats ${member}`);
    const size = octal(124, 12);
    const start = offset + 512;
    if (start + size > bytes.length) throw new Error(`${recordId}: references layer is truncated inside ${member}`);
    members.set(member, bytes.subarray(start, start + size));
    if (members.size > MAX_CAPTURE_FILES) throw new Error(`${recordId}: references layer has too many members`);
    offset = start + Math.ceil(size / 512) * 512;
  }
}

/** The cached layer, verified again against the record, or nothing. */
function cachedLayer(directory: string, layer: CaptureReferences): LayerMembers | undefined {
  const location = referenceLayerPath(directory, layer.digest);
  if (!fs.existsSync(location)) return undefined;
  if (fs.statSync(location).size !== layer.bytes) throw new Error(`references layer cache size mismatch for ${layer.digest}`);
  return verifiedLayer(fs.readFileSync(location), layer, layer.digest.slice(0, 12));
}

/** Every concept's references from a verified layer: the source member must
 * be byte-equal to the displayed `sourceText` — the layer doubles as the
 * check that the shown source is what the archive built — and the `.ilean`
 * member must parse against it. */
function layerReferences(submission: SiteSubmission, members: LayerMembers): Map<string, LeanReferences> {
  const result = new Map<string, LeanReferences>();
  for (const concept of submission.output!.concepts) {
    const paths = memberPaths(concept);
    const source = members.get(paths.source);
    const metadata = members.get(paths.metadata);
    if (!source || !source.equals(Buffer.from(concept.sourceText)))
      throw new Error(`${concept.id}: references layer does not match displayed source`);
    if (!metadata || metadata.length > MAX_REFERENCE_BYTES || !metadata.length)
      throw new Error(`${concept.id}: references layer lacks a supported .ilean member`);
    result.set(concept.id, parseLeanReferences(metadata.toString("utf8"), concept.id, concept.sourceText));
  }
  return result;
}

function loadReferencesFromLayer(submission: SiteSubmission, layer: CaptureReferences, directory: string): Map<string, LeanReferences> {
  const members = cachedLayer(directory, layer);
  if (!members) throw new Error(`${submission.record.id}: references cache is missing layer ${layer.digest}; run \`npm run references:fetch\``);
  return layerReferences(submission, members);
}
