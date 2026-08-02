import fs from "node:fs";
import path from "node:path";
import type { BuildOutput, DbRecord } from "./types.js";
import type { SiteSubmission } from "./sitegen/model.js";

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
      return [{ record, output }];
    });
}
