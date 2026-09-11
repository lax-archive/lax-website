/** Build-time cache of the compiler's reference maps from sealed captures.
 * Captures are deterministic, uncompressed ustar. Read bounded byte ranges
 * for just the .ilean members, verifying their headers and recorded SHA-256;
 * never extract a tar or download/execute the submission's proof artifacts. */
import { createHash, randomUUID } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { MAX_REFERENCE_BYTES, parseLeanReferences, type LeanReferences } from "./lean-references.js";
import { BLOB_REFERENCE, downloadBlob, type FetchOptions } from "./papers.js";
import type { SiteSubmission } from "./sitegen/model.js";
import type { CaptureEntry, CaptureFile, ConceptEntry } from "./types.js";

const SHA256 = /^[0-9a-f]{64}$/u;
const MAX_CAPTURE_BYTES = 2 * 1024 ** 3;
const MAX_CAPTURE_FILES = 100_000;
const sha256 = (bytes: string | Buffer): string => createHash("sha256").update(bytes).digest("hex");

export function referenceCachePath(directory: string, digest: string): string {
  if (!SHA256.test(digest)) throw new Error("reference digest is not sha256 hex");
  return path.join(path.resolve(directory), `${digest}.ilean`);
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

interface ReferenceJob { concept: ConceptEntry; file: CaptureFile }
function jobs(submission: SiteSubmission): { capture: CaptureEntry; files: Map<string, CaptureFile>; wanted: ReferenceJob[] } | undefined {
  const output = submission.output;
  const capture = output?.capture;
  if (submission.record.state === "deleted" || !output?.concepts.length || !capture ||
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
