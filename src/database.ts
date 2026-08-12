import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import type { BuildOutput, CaptureFile, CaptureManifest, DbRecord } from "./types.js";
import type { SiteSubmission, SourceIntegrity } from "./sitegen/model.js";

function readJson<T>(file: string): T | undefined {
  if (!fs.existsSync(file)) return undefined;
  return JSON.parse(fs.readFileSync(file, "utf8")) as T;
}

function isObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
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
  return output as unknown as BuildOutput;
}

const SHA256 = /^[0-9a-f]{64}$/;
const COMMIT = /^[0-9a-f]{40}$/;

function checkedCapture(value: CaptureManifest | undefined, label: string): CaptureManifest {
  if (!isObject(value)) throw new Error(`${label} has no validation capture`);
  if (value.formatVersion !== 1) throw new Error(`${label} capture formatVersion must be 1`);
  if (typeof value.digest !== "string" || !SHA256.test(value.digest))
    throw new Error(`${label} capture digest must be a lowercase SHA-256`);
  if (typeof value.sourceCommit !== "string" || !COMMIT.test(value.sourceCommit))
    throw new Error(`${label} capture sourceCommit must be a lowercase Git commit`);
  if (!Array.isArray(value.files)) throw new Error(`${label} capture files must be an array`);
  return value;
}

function captureFiles(capture: CaptureManifest, label: string): Map<string, CaptureFile> {
  const files = new Map<string, CaptureFile>();
  for (const file of capture.files) {
    if (!isObject(file) || typeof file.path !== "string" || !file.path.length)
      throw new Error(`${label} capture contains an invalid file path`);
    if (!Number.isSafeInteger(file.bytes) || file.bytes < 0)
      throw new Error(`${label} capture file ${file.path} has an invalid byte count`);
    if (typeof file.sha256 !== "string" || !SHA256.test(file.sha256))
      throw new Error(`${label} capture file ${file.path} has an invalid SHA-256`);
    if (files.has(file.path)) throw new Error(`${label} capture repeats file ${file.path}`);
    files.set(file.path, file as CaptureFile);
  }
  return files;
}

function packageFile(kind: "concepts" | "proofs", declaredPath: string, label: string): string {
  const prefix = `${kind}/`;
  if (!declaredPath.startsWith(prefix) || declaredPath.includes("\\") || declaredPath.split("/").includes(".."))
    throw new Error(`${label} path must stay below ${prefix}`);
  return `${kind}/package/${declaredPath.slice(prefix.length)}`;
}

/** Bind every rendered source to the exact immutable capture checked for the
 * advertised repository commit. A mismatch is a publication failure, never
 * something the renderer should silently display. */
function sourceIntegrity(record: DbRecord, output: BuildOutput, label: string): SourceIntegrity {
  const source = record.source;
  if (!source) throw new Error(`${label} has rendered output but no pinned source commit`);
  if (output.id !== record.id) throw new Error(`${label} output id ${output.id} does not match record id ${record.id}`);
  const capture = checkedCapture(output.capture, label);
  if (capture.sourceCommit !== source.commit)
    throw new Error(`${label} capture commit ${capture.sourceCommit} does not match record commit ${source.commit}`);
  const files = captureFiles(capture, label);
  const conceptFiles: Record<string, CaptureFile> = {};
  for (const concept of output.concepts) {
    const capturePath = packageFile("concepts", concept.path, `concept ${concept.id}`);
    const file = files.get(capturePath);
    if (!file) throw new Error(`${label} capture does not contain rendered concept ${capturePath}`);
    const bytes = Buffer.byteLength(concept.sourceText, "utf8");
    const sha256 = createHash("sha256").update(concept.sourceText, "utf8").digest("hex");
    if (file.bytes !== bytes || file.sha256 !== sha256)
      throw new Error(`${label} rendered concept ${concept.id} does not match capture file ${capturePath}`);
    conceptFiles[concept.id] = file;
  }
  const proofFiles: Record<string, CaptureFile> = {};
  for (const proof of output.proofs) {
    const capturePath = packageFile("proofs", proof.path, `proof ${proof.id}`);
    const file = files.get(capturePath);
    if (!file) throw new Error(`${label} capture does not contain proof source ${capturePath}`);
    proofFiles[proof.id] = file;
  }
  return {
    captureDigest: capture.digest,
    sourceCommit: capture.sourceCommit,
    conceptFiles,
    proofFiles,
  };
}

/**
 * Read the checked-out public archive database. The website never mutates
 * this input and deliberately needs no access to server operational state.
 */
export function loadSubmissions(databaseDir: string): SiteSubmission[] {
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
      const integrity = output ? sourceIntegrity(record, output, outputFile) : undefined;
      return [{ record, output, integrity }];
    });
}
