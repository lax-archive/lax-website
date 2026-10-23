import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { dottedIdentifierPrefix, identifierComponents, leanHoverTokens, nameKey, nameParts, scanLeanSource, type SourceRange } from "./lean-source.js";
import type { SiteModel } from "./model.js";
import { CONE_EXPORT_VERSION, CONE_EXTRACTION_VERSION, validateConeModule, verifiedConeFile, coneDeclarations, type ConeModule } from "./dependency-cones.js";

export interface SourceHover extends SourceRange {
  text: string;
  /** Compiler-resolved notation destination, independent of host paths. */
  definition?: { module: string; name: string; line: number };
}
export interface LeanCodeData {
  version: 1;
  projectionHovers?: 1;
  numericHovers?: 1;
  digest: string;
  hovers: SourceHover[];
  cones?: ConeModule;
}

/** Changing the extractor or pretty-print options invalidates prepared data. */
export const LEAN_CODE_VERSION = "lean-hover-4";

export function leanCodeInputs(model: SiteModel, id: string): { digest: string; modules: string[] } {
  const modules: string[] = [], active = new Set<string>(), seen = new Set<string>();
  const visit = (name: string) => {
    if (active.has(name)) throw new Error(`cyclic Lean imports at ${name}`);
    if (seen.has(name)) return;
    const located = model.conceptHome.get(name);
    if (!located) throw new Error(`missing Lean import ${name}`);
    active.add(name);
    for (const imported of located.concept.imports) visit(imported);
    active.delete(name); seen.add(name); modules.push(name);
  };
  visit(id);
  const input = modules.map((name) => {
    const { concept, output } = model.conceptHome.get(name)!;
    return [name, concept.sourceText, output.manifest.leanVersion, output.manifest.mathlibVersion];
  });
  return { modules, digest: createHash("sha256").update(JSON.stringify([LEAN_CODE_VERSION, input])).digest("hex") };
}

export function parseLeanCode(json: string, digest: string, source: string): LeanCodeData {
  const data = JSON.parse(json) as LeanCodeData;
  const sourceTokens = leanHoverTokens(scanLeanSource(source));
  if (data.numericHovers !== 1 && sourceTokens.some(token => token.number))
    throw new Error("missing Lean numeric hovers");
  const receivers = new Set<string>();
  const notations = new Set(sourceTokens.filter(t => t.notation).map(t => `${t.start}:${t.end}`));
  const tokens = new Set(sourceTokens.flatMap(token => {
    const prefix = dottedIdentifierPrefix(token);
    if (prefix) receivers.add(`${prefix.start}:${prefix.end}`);
    return [token, ...identifierComponents(token)].map(range => `${range.start}:${range.end}`);
  }));
  let end = 0;
  if (data.version !== 1 || data.digest !== digest || !Array.isArray(data.hovers))
    throw new Error("stale Lean hover cache");
  for (const hover of data.hovers) {
    // Refresh only older modules with receiver hovers: their field/method
    // suffixes were never queried. Namespace-only caches remain reusable.
    if (data.projectionHovers !== 1 && receivers.has(`${hover.start}:${hover.end}`))
      throw new Error("missing Lean projection hovers");
    if (!tokens.has(`${hover.start}:${hover.end}`) || hover.start < end ||
        typeof hover.text !== "string" || !hover.text.trim() || hover.text.length > 32768)
      throw new Error("invalid Lean hover range or type");
    if (hover.definition && (!notations.has(`${hover.start}:${hover.end}`) ||
        typeof hover.definition.module !== "string" || !/^[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*$/.test(hover.definition.module) ||
        typeof hover.definition.name !== "string" || !hover.definition.name.trim() ||
        !Number.isSafeInteger(hover.definition.line) || hover.definition.line < 1))
      throw new Error("invalid Lean notation destination");
    end = hover.end;
  }
  if (data.cones !== undefined) validateConeModule(data.cones, source);
  return data;
}

export function requireCones(data: LeanCodeData, source: string, directory: string): void {
  if (!data.cones?.exports || data.cones.exportVersion !== CONE_EXPORT_VERSION || data.cones.extractionVersion !== CONE_EXTRACTION_VERSION)
    throw new Error("missing or stale dependency cones");
  const exports = new Map(data.cones.exports.map(entry => [entry.name, entry.digest]));
  for (const declaration of coneDeclarations(data.cones, source)) {
    const digest = exports.get(declaration.name);
    if (!digest) throw new Error(`missing dependency cone for ${declaration.name}`);
    verifiedConeFile(directory, digest);
  }
}

export function loadLeanCode(model: SiteModel, directory: string, required = false): void {
  const statements = new Set([...model.conceptHome.values()].flatMap(({ concept }) =>
    concept.statements.map(statement => nameKey(nameParts(statement.id)))));
  for (const [id, { concept }] of model.conceptHome) {
    const { digest } = leanCodeInputs(model, id);
    try {
      const data = parseLeanCode(fs.readFileSync(path.join(directory, `${digest}.json`), "utf8"), digest, concept.sourceText);
      try { requireCones(data, concept.sourceText, directory); }
      catch (error) {
        if (required) throw error;
        // Local rendering can reuse types while cone preparation is pending.
        delete data.cones;
      }
      // Compiler signatures start with the resolved declaration name. Match
      // its full name, so imported statements are excluded too, while local
      // variables with the same short spelling retain their type hovers.
      model.leanCode.set(id, { ...data, hovers: data.hovers.filter(hover => {
        const name = scanLeanSource(hover.text).tokens[0]?.name;
        return hover.definition || !name || !statements.has(nameKey(name));
      }) });
    } catch (error) {
      if (required) throw new Error(`${id}: run npm run lean:prepare to refresh types and dependency cones (${error})`);
    }
  }
}
