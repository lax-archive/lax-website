import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { scanLeanSource, type SourceRange } from "./lean-source.js";
import type { SiteModel } from "./model.js";
import { attr, esc } from "./html.js";

export interface SourceHover extends SourceRange { text: string }
export interface LeanCodeData {
  version: 1;
  digest: string;
  hovers: SourceHover[];
}

/** Changing the extractor or pretty-print options invalidates prepared data. */
export const LEAN_CODE_VERSION = "lean-hover-1";

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
  const tokens = new Set(scanLeanSource(source).tokens.filter(t => t.name).map(t => `${t.start}:${t.end}`));
  let end = 0;
  if (data.version !== 1 || data.digest !== digest || !Array.isArray(data.hovers))
    throw new Error("stale Lean hover cache");
  for (const hover of data.hovers) {
    if (!tokens.has(`${hover.start}:${hover.end}`) || hover.start < end ||
        typeof hover.text !== "string" || !hover.text.trim() || hover.text.length > 32768)
      throw new Error("invalid Lean hover range or type");
    end = hover.end;
  }
  return data;
}

export function loadLeanCode(model: SiteModel, directory: string, required = false): void {
  for (const [id, { concept }] of model.conceptHome) {
    const { digest } = leanCodeInputs(model, id);
    try {
      model.leanCode.set(id, parseLeanCode(fs.readFileSync(path.join(directory, `${digest}.json`), "utf8"), digest, concept.sourceText));
    } catch (error) {
      if (required) throw new Error(`${id}: run npm run lean:prepare to refresh type hovers (${error})`);
    }
  }
}

/** A portable editor document. Module-local commands remain scoped; imports
 * are lifted once. Comments are omitted, including submission annotations.
 * Unsupported module/private syntax keeps the original source download only. */
export function liveLeanCode(model: SiteModel, id: string): string | undefined {
  const { modules } = leanCodeInputs(model, id);
  const imports = new Set<string>();
  const bodies: string[] = [];
  for (const name of modules) {
    const { sourceText } = model.conceptHome.get(name)!.concept;
    const parsed = scanLeanSource(sourceText);
    if (parsed.tokens.some(t => ["private", "module", "public", "initialize", "builtin_initialize"].includes(t.text))) return;
    let source = sourceText;
    for (const comment of [...parsed.comments].reverse())
      source = source.slice(0, comment.start) + source.slice(comment.start, comment.end).replace(/[^\r\n]/g, " ") + source.slice(comment.end);
    source = source.replace(/^\s*import\s+([^\r\n]+)/gm, (_, names: string) => {
      for (const imported of names.trim().split(/\s+/)) if (!model.conceptHome.has(imported)) imports.add(imported);
      return "";
    });
    bodies.push(`-- ${name}\nsection\n${source.trim()}\nend`);
  }
  return `${[...imports].sort().map(name => `import ${name}`).join("\n")}\n\n${bodies.join("\n\n")}\n`;
}

export function liveLeanLink(model: SiteModel, id: string): string {
  let source: string | undefined;
  // Incomplete local previews can still show source and archive navigation.
  try { source = liveLeanCode(model, id); } catch { return ""; }
  if (!source) return "";
  const version = model.conceptHome.get(id)!.output.manifest.leanVersion;
  const mathlib = /^import (?!Lean(?:\.|$)|Init(?:\.|$)|Std(?:\.|$))/m.test(source);
  // live.lean-lang.org's configured projects, verified 2026-09-14. Its stable
  // Mathlib is v4.33.0; older Mathlib releases are not all hosted there.
  const project = mathlib ? "mathlib-stable" : `lean-${version}`;
  const note = mathlib && version !== "v4.33.0" ? " (Mathlib 4.33)" : "";
  return `<a class="source-link lean-live-link" href="${attr(`https://live.lean-lang.org/#project=${encodeURIComponent(project)}&code=${encodeURIComponent(source)}`)}" target="_blank" rel="noopener noreferrer">Open in live Lean${esc(note)}</a>`;
}
