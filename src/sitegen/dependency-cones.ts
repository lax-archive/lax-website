import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import type { SiteModel } from "./model.js";
import { leanDeclarations, nameKey, nameParts, scanLeanSource, type SourceRange } from "./lean-source.js";

/** Compiler commands are indivisible: a structure, mutual block, or command
 * macro can define several constants, including generated helpers. */
export interface ConeCommand extends SourceRange { kind: string; uses: string[]; expanded?: string }
export interface ConeDeclaration {
  name: string; command: number; dependencies: string[]; selection?: SourceRange;
}
export interface ConeModule {
  version: 1;
  commands: ConeCommand[];
  declarations: ConeDeclaration[];
  namespaces: string[];
  /** Resolved source identifiers used when combined imports change name resolution. */
  references?: (SourceRange & { name: string })[];
  extractionVersion?: number;
  /** Only files successfully elaborated in the pinned environment appear here. */
  exports?: { name: string; digest: string }[];
  exportVersion?: number;
}
export interface DeclarationAction extends SourceRange { name: string; href: string }

export const CONE_VERSION = 1;
export const CONE_EXTRACTION_VERSION = 3;
export const CONE_EXPORT_VERSION = 4;
const SHA256 = /^[0-9a-f]{64}$/;
export const coneDigest = (source: string): string => createHash("sha256").update(source).digest("hex");
export const coneCacheFile = (cache: string, digest: string): string => {
  if (!SHA256.test(digest)) throw new Error("invalid dependency cone digest");
  return path.join(cache, "cones", `${digest}.lean`);
};

const sourceInventories = new WeakMap<SiteModel, Map<string, {
  source: string; namespaces: Set<string>; declaredNamespaces: Set<string>; identifiers: Map<number, number>;
  instanceCommands: Set<number>;
}>>();

/** A module can contain thousands of roots. Scan its source once, not once
 * per export, and retain only the namespace and bare-identifier positions. */
function sourceInventory(model: SiteModel, module: string, source: string) {
  let modules = sourceInventories.get(model);
  if (!modules) { modules = new Map(); sourceInventories.set(model, modules); }
  let inventory = modules.get(module);
  if (inventory?.source === source) return inventory;
  const scanned = scanLeanSource(source), namespaces = new Set<string>();
  leanDeclarations(scanned, undefined, ref => {
    if (ref.kind === "namespace") namespaces.add(nameKey(ref.namespace));
  });
  const declaredNamespaces = new Set(namespaces);
  const data = model.leanCode.get(module)?.cones;
  if (data) for (const declaration of coneDeclarations(data, source)) {
    if (declaration.name.startsWith("_private.")) continue;
    const parts = nameParts(declaration.name);
    for (let n = 1; n <= parts.length; n++) declaredNamespaces.add(nameKey(parts.slice(0, n)));
  }
  // Coercion instances can reduce away during elaboration. Their names then
  // disappear from kernel dependencies, while the original source still
  // needs them. Include explicit, attributed and deriving instance commands.
  const instanceCommands = new Set<number>();
  let command = 0;
  if (data) for (const token of scanned.tokens) {
    if (token.text !== "instance") continue;
    while (data.commands[command] && data.commands[command]!.end <= token.start) command++;
    if (data.commands[command] && data.commands[command]!.start <= token.start) instanceCommands.add(command);
  }
  inventory = { source, namespaces, declaredNamespaces,
    identifiers: new Map(scanned.tokens.filter(t => t.name?.length === 1).map(t => [t.start, t.end])), instanceCommands };
  modules.set(module, inventory); return inventory;
}

export function validateConeModule(value: ConeModule, source: string): void {
  const range = (r: SourceRange) => Number.isSafeInteger(r.start) && Number.isSafeInteger(r.end) &&
    r.start >= 0 && r.end > r.start && r.end <= source.length;
  const names = (v: unknown): v is string[] => Array.isArray(v) && v.every(n => typeof n === "string" && n.length > 0);
  if (!value || value.version !== CONE_VERSION || !Array.isArray(value.commands) || !Array.isArray(value.declarations) || !names(value.namespaces))
    throw new Error("unsupported dependency cone metadata");
  let end = 0;
  for (const command of value.commands) {
    if (!range(command) || command.start < end || typeof command.kind !== "string" || !names(command.uses) ||
        (command.expanded !== undefined && typeof command.expanded !== "string"))
      throw new Error("invalid dependency cone command");
    end = command.end;
  }
  const seen = new Set<string>();
  for (const declaration of value.declarations) {
    const command = value.commands[declaration.command];
    if (typeof declaration.name !== "string" || !declaration.name || seen.has(declaration.name) ||
        !Number.isSafeInteger(declaration.command) || !command || !names(declaration.dependencies) ||
        (declaration.selection && (!range(declaration.selection) || declaration.selection.start < command.start || declaration.selection.end > command.end)))
      throw new Error("invalid dependency cone declaration");
    seen.add(declaration.name);
  }
  const exported = new Set<string>();
  for (const entry of value.exports ?? []) {
    if (!seen.has(entry.name) || exported.has(entry.name) || !SHA256.test(entry.digest))
      throw new Error("invalid dependency cone export");
    exported.add(entry.name);
  }
  for (const ref of value.references ?? [])
    if (!range(ref) || typeof ref.name !== "string" || !ref.name) throw new Error("invalid dependency cone reference");
}

/** Generated helpers often reuse their parent's selection. Only the actual
 * written name is an action, including fields, constructors and instances. */
export function coneDeclarations(data: ConeModule, source: string): ConeDeclaration[] {
  const seen = new Set<string>();
  return data.declarations.filter(declaration => {
    const selection = declaration.selection;
    if (!selection) return false;
    const text = source.slice(selection.start, selection.end);
    const parts = nameParts(text), names = nameParts(declaration.name);
    if (!parts.length || parts.at(-1) !== names.at(-1) || !scanLeanSource(text).tokens[0]?.name) return false;
    const key = `${selection.start}:${selection.end}`;
    if (seen.has(key)) return false;
    seen.add(key); return true;
  });
}

export function declarationActions(model: SiteModel, module: string, rootRel: string): DeclarationAction[] {
  const home = model.conceptHome.get(module), data = model.leanCode.get(module)?.cones;
  if (!home || !data?.exports) return [];
  const exports = new Map(data.exports.map(e => [e.name, e.digest]));
  return coneDeclarations(data, home.concept.sourceText).flatMap(d => {
    const digest = exports.get(d.name);
    return digest ? [{ ...d.selection!, name: d.name,
      href: `${rootRel}${home.output.id}/cones/${digest}.lean` }] : [];
  });
}

/** Preserve source commands, using checked expansions for custom commands
 * whose elaborators may rely on separate module initialization. */
export function dependencyCone(model: SiteModel, rootModule: string, rootName: string, qualify = false): string {
  const ordered: string[] = [], modules = new Set<string>();
  const visitModule = (id: string) => {
    if (modules.has(id)) return;
    modules.add(id);
    const home = model.conceptHome.get(id);
    if (!home) throw new Error(`missing dependency cone module ${id}`);
    home.concept.imports.forEach(visitModule); ordered.push(id);
  };
  visitModule(rootModule);
  const names = new Map<string, { module: string; declaration: ConeDeclaration }>();
  const units = new Map<string, Map<number, ConeDeclaration[]>>();
  for (const module of ordered) {
    const data = model.leanCode.get(module)?.cones;
    if (!data) throw new Error(`missing dependency cone metadata for ${module}`);
    const groups = new Map<number, ConeDeclaration[]>();
    for (const declaration of data.declarations) {
      names.set(declaration.name, { module, declaration });
      const group = groups.get(declaration.command) ?? [];
      group.push(declaration); groups.set(declaration.command, group);
    }
    units.set(module, groups);
  }
  if (!names.has(rootName)) throw new Error(`missing dependency cone root ${rootName}`);
  const included = new Map<string, Set<number>>();
  const pending = [rootName];
  const environmentCommand = (kind: string) => /^Lean\.Parser\.Command\.(?:syntax|macro|macro_rules|elab|elab_rules|initialize|notation|mixfix|infixl?|infixr|prefix|postfix|declare_syntax_cat|register_option|attribute|export)$/.test(kind);
  const select = (module: string, index: number) => {
    const selected = included.get(module) ?? new Set<number>();
    if (selected.has(index)) return;
    const first = !included.has(module);
    selected.add(index); included.set(module, selected);
    const data = model.leanCode.get(module)!.cones!;
    pending.push(...data.commands[index]!.uses);
    for (const decl of units.get(module)!.get(index) ?? []) pending.push(...decl.dependencies);
    if (first) data.commands.forEach((cmd, i) => {
      if (!units.get(module)!.has(i) && !/(?:moduleDoc|check|eval|print|example|run_cmd|runTermElab)/.test(cmd.kind)) select(module, i);
    });
  };
  // Imported syntax and elaborators affect parsing even when their generated
  // constants do not occur in the resulting kernel expressions. Retain their
  // commands and dependencies, together with each module's scope context.
  for (const module of ordered) {
    const source = model.conceptHome.get(module)!.concept.sourceText;
    const instances = sourceInventory(model, module, source).instanceCommands;
    model.leanCode.get(module)!.cones!.commands.forEach((cmd, i) => {
      if (environmentCommand(cmd.kind) || instances.has(i)) select(module, i);
    });
  }
  while (pending.length) {
    const name = pending.pop()!, found = names.get(name);
    if (found) select(found.module, found.declaration.command);
    else if (/^(?:_private\.)?Lax\d+\./.test(name)) throw new Error(`unresolved archive declaration ${name}`);
  }
  const imports = new Set<string>();
  const bodies: string[] = [];
  // Kernel expansions do not carry the separate runtime implementations Lean
  // generates for recursion. Let Lean retain their mathematical definitions
  // without requiring those compiler-only implementations downstream.
  const section = [...included].some(([module, commands]) => [...commands].some(i =>
    model.leanCode.get(module)!.cones!.commands[i]!.expanded)) ? "noncomputable section" : "section";
  for (const module of ordered) {
    const { concept } = model.conceptHome.get(module)!;
    for (const imported of concept.mathlibImports ?? []) imports.add(imported);
    const data = model.leanCode.get(module)!.cones!;
    const selected = included.get(module);
    // `open A` is valid even if none of A's declarations are needed. Preserve
    // the namespace without pulling otherwise unrelated declarations in.
    const inventory = sourceInventory(model, module, concept.sourceText);
    const provided = new Set(selected ? inventory.namespaces : []);
    if (selected) {
      for (const decl of data.declarations) if (selected.has(decl.command)) {
        const parts = nameParts(decl.name);
        for (let n = 1; n <= parts.length; n++) provided.add(nameKey(parts.slice(0, n)));
      }
    }
    // Namespace stubs come from written names, never compiler-generated
    // helper namespaces (which can contain process-specific source paths).
    const namespaces = data.namespaces.filter(n => {
      const key = nameKey(nameParts(n));
      return inventory.declaredNamespaces.has(key) && !provided.has(key);
    })
      .map(n => `namespace ${n}\nend ${n}`);
    const commands = [...selected ?? []].sort((a, b) => a - b).map(i => {
      const command = data.commands[i]!;
      if (command.expanded) return `-- Expanded from ${command.kind}\n${command.expanded}`;
      let text = concept.sourceText.slice(command.start, command.end);
      // Combining import environments can change resolution of a bare name
      // (e.g. FirstOrder.Language versus the global language-of-words type).
      // On validation failure, retry using the compiler's original names.
      if (qualify && !environmentCommand(command.kind)) {
        const refs = new Map<number, { end: number; name: string }>();
        for (const ref of data.references ?? []) {
          if (ref.start < command.start || ref.end > command.end || names.has(ref.name) ||
              ref.name.startsWith("_private.") || ref.name.startsWith("Lean.Parser.Category.")) continue;
          if (nameParts(ref.name).at(-1) !== nameParts(concept.sourceText.slice(ref.start, ref.end)).at(-1)) continue;
          if (inventory.identifiers.get(ref.start) === ref.end && concept.sourceText[ref.start - 1] !== ".") refs.set(ref.start, ref);
        }
        for (const [start, ref] of [...refs].sort(([a], [b]) => b - a))
          text = text.slice(0, start - command.start) + `_root_.${ref.name}` + text.slice(ref.end - command.start);
      }
      return text;
    });
    if (namespaces.length || commands.length)
      bodies.push(`-- ${module}\n${section}\n${[...namespaces, ...commands].join("\n\n")}\nend`);
  }
  const { manifest } = model.conceptHome.get(rootModule)!.output;
  return `-- Lax dependency cone\n-- Lean: ${manifest.leanVersion}\n-- Mathlib: ${manifest.mathlibVersion}\n\n` +
    [...imports].sort().map(name => `import ${name}`).join("\n") + "\n\n" + bodies.join("\n\n") + "\n";
}

export function verifiedConeFile(cache: string, digest: string): string {
  const file = coneCacheFile(cache, digest);
  if (coneDigest(fs.readFileSync(file, "utf8")) !== digest) throw new Error(`dependency cone digest mismatch: ${digest}`);
  return file;
}
