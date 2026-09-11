import { leanDeclarations, nameKey, nameParts, scanLeanSource, type LeanNamespaceReference, type LeanSource, type LeanToken, type SourceRange } from "./lean-source.js";
import type { LocatedConcept, SiteModel } from "./model.js";
import type { LeanReferences } from "../lean-references.js";

export interface SourceLink extends SourceRange { href: string }
interface Target { module: string; href: string; offset: number; private: boolean }
interface Reference { token: LeanToken; namespace: readonly string[] }
interface ModuleSource {
  references: Reference[];
  locals: Set<string>;
  semantic?: LeanReferences;
  definitionSites: SourceRange[];
  imports: SourceLink[];
  namespaces: LeanNamespaceReference[];
}

/** Even dotted syntax can be local: `let N.value := ...; N.value`, or a
 * projection through a binder named N. Suppress these spellings throughout
 * the file; narrowing their scopes would require elaborated references. */
function possibleLocals(source: LeanSource, declarations: Set<number>): Set<string> {
  const locals = new Set<string>();
  const bind = (index: number) => {
    const token = source.tokens[index]!;
    if (token.name && !declarations.has(token.start)) locals.add(token.name[0]!);
  };
  let header = false;
  let patternLine = -1;
  let depth = 0;
  for (let i = 0; i < source.tokens.length; i++) {
    const token = source.tokens[i]!;
    if (patternLine >= 0 && token.line !== patternLine) { header = false; patternLine = -1; }
    if (token.text === "|" || ["intro", "intros", "rintro", "rcases", "cases", "induction", "case", "rename_i"].includes(token.text)) {
      header = true;
      depth = 0;
      patternLine = token.line;
      continue;
    }
    if (["let", "letI", "letI'", "let'", "have", "haveI", "suffices", "obtain", "fun", "∀", "∃", "λ"].includes(token.text)) {
      header = true;
      depth = 0;
      patternLine = -1;
      continue;
    }
    if (token.text === ":" || token.text === "←" || (token.text === "=" && source.tokens[i + 1]?.text === ">")) {
      for (let before = i - 1; before >= 0 && source.tokens[before]!.name; before--) {
        const previous = source.tokens[before]!;
        if (declarations.has(previous.start) || ["example", "instance", "variable", "variables"].includes(previous.text)) break;
        bind(before);
      }
      header = false;
    }
    if (!header) continue;
    if (["(", "[", "{", "⦃", "⟨"].includes(token.text)) depth++;
    if ([")", "]", "}", "⦄", "⟩"].includes(token.text)) depth--;
    if ((token.text === "," && depth === 0) || token.text === "in" || token.text === "=" || token.text === "←") header = false;
    else bind(i);
  }
  return locals;
}

/** One inventory per immutable build model. A paper can repeat a concept:
 * share both the scanned source and its resolved links with the concept page. */
const indexes = new WeakMap<SiteModel, SourceLinkIndex>();

class SourceLinkIndex {
  private readonly modules = new Map<string, ModuleSource>();
  private readonly names = new Map<string, Target[]>();
  private readonly semanticTargets = new Map<string, Map<string, string>>();
  private readonly namespaceHomes = new Map<string, Map<string, string>>();
  private readonly submissionNamespaces = new Map<string, string>();
  private readonly resolved = new Map<string, SourceLink[]>();

  constructor(private readonly model: SiteModel) {
    for (const { record } of model.submissions) {
      const number = /^(?:lax-|Lax)([0-9]+)$/u.exec(record.id)?.[1];
      if (number) this.submissionNamespaces.set(nameKey([`Lax${number}`]), `${encodeURIComponent(record.id)}/index.html`);
    }
    for (const located of model.conceptHome.values()) {
      const { concept } = located;
      const source = scanLeanSource(concept.sourceText);
      const references: Reference[] = [];
      const semantic = located.submission.sourceReferences?.get(concept.id);
      const namespaces: LeanNamespaceReference[] = [];
      const inventory = leanDeclarations(source, semantic ? undefined : (token, namespace) => references.push({ token, namespace }),
        (reference) => namespaces.push(reference));
      const declarations = new Set(inventory.map((declaration) => declaration.token.start));
      const statements = new Map(concept.statements.map((s) => [nameKey(nameParts(s.id)), s]));
      const statementsById = new Map(concept.statements.map((statement) => [statement.id, statement]));
      for (const declaration of inventory) {
        const key = nameKey(declaration.name);
        const statement = statements.get(key);
        const fragment = statement?.startLine !== undefined ? `s-${statement.id}` : `L${declaration.startLine}`;
        const target = { module: concept.id, href: `${this.page(located)}#${encodeURIComponent(fragment)}`,
          offset: declaration.token.start, private: declaration.private };
        const candidates = this.names.get(key) ?? [];
        candidates.push(target);
        this.names.set(key, candidates);
      }
      const definitionSites: SourceRange[] = inventory.map((entry) => entry.token);
      if (semantic) {
        const targets = new Map<string, string>();
        const firstOnLine = new Map<number, LeanToken>();
        for (const token of source.tokens) if (!firstOnLine.has(token.line)) firstOnLine.set(token.line, token);
        const preambles = new Map(inventory.map((entry) => [entry.token.start, entry.startLine]));
        const definitions = new Map(semantic.constants.flatMap((ref) =>
          ref.definition ? [[ref.name, ref.definition] as const] : []));
        for (const [name, declaration] of semantic.declarations)
          if (!definitions.has(name)) definitions.set(name, declaration.selection);
        for (const [name, definition] of definitions) {
          if (definition.start < definition.end) definitionSites.push(definition);
          const declaration = semantic.declarations.get(name);
          const line = Math.min(definition.line, declaration?.range.line ?? definition.line,
            preambles.get(definition.start) ?? firstOnLine.get(definition.line)?.leadingCommentLine ?? definition.line);
          const statement = statementsById.get(name);
          const fragment = statement?.startLine !== undefined ? `s-${statement.id}` : `L${line}`;
          targets.set(name, `${this.page(located)}#${encodeURIComponent(fragment)}`);
        }
        this.semanticTargets.set(concept.id, targets);
      }
      const imports: SourceLink[] = [];
      const imported = new Set(concept.imports);
      for (let i = 0; i < source.tokens.length; i++) {
        if (source.tokens[i]!.text !== "import") continue;
        for (let j = i + 1; j < source.tokens.length; j++) {
          const token = source.tokens[j]!;
          if (token.text === "all") continue;
          if (!imported.has(token.text)) break;
          const target = model.conceptHome.get(token.text);
          if (target) imports.push({ start: token.start, end: token.end, href: this.page(target) });
        }
      }
      this.modules.set(concept.id, {
        references, locals: semantic ? new Set() : possibleLocals(source, declarations),
        semantic, definitionSites, imports, namespaces,
      });
      const addNamespace = (parts: readonly string[]) => {
        const key = nameKey(parts);
        const homes = this.namespaceHomes.get(key) ?? new Map<string, string>();
        const declaration = this.semanticTargets.get(concept.id)?.get(parts.join(".")) ??
          (this.names.get(key) ?? []).find((target) => target.module === concept.id)?.href;
        homes.set(concept.id, declaration ?? this.page(located));
        this.namespaceHomes.set(key, homes);
      };
      const addPrefixes = (parts: readonly string[]) => {
        for (let end = 1; end <= parts.length; end++) addNamespace(parts.slice(0, end));
      };
      addPrefixes(nameParts(concept.id));
      for (const ref of namespaces) if (ref.kind === "namespace") addPrefixes(ref.namespace);
      const names = semantic ? [...semantic.declarations.keys(), ...semantic.constants.filter((ref) => ref.definition).map((ref) => ref.name)]
        .map(nameParts) : inventory.map((declaration) => declaration.name);
      for (const parts of names) addPrefixes(parts);
    }
  }

  private page({ output, concept }: LocatedConcept): string {
    return `${encodeURIComponent(output.id)}/${encodeURIComponent(concept.id)}.html`;
  }

  /** The compiler gives the owning module and exact declaration name. For
   * generated constructors/recursors without their own source, navigate to
   * the nearest enclosing declaration (or the module if none has a span). */
  private semanticTarget(module: string, name: string): string | undefined {
    const located = this.model.conceptHome.get(module);
    if (!located) return undefined; // Mathlib/Lean and other non-archive code.
    const targets = this.semanticTargets.get(module);
    for (let parent = name; parent; parent = parent.slice(0, parent.lastIndexOf("."))) {
      const target = targets?.get(parent);
      if (target) return target;
      if (!parent.includes(".")) break;
    }
    return this.page(located);
  }

  private namespaceLinks(source: ModuleSource, visible: Set<string>): SourceLink[] {
    const links: SourceLink[] = [];
    for (const reference of source.namespaces) {
      const { token, namespace, kind } = reference;
      let href: string | undefined;
      if (kind !== "open") href = this.submissionNamespaces.get(nameKey(namespace));
      else {
        const rooted = token.name![0] === "_root_";
        const parts = rooted ? token.name!.slice(1) : token.name!;
        for (let depth = rooted ? 0 : namespace.length; depth >= 0; depth--) {
          const key = nameKey([...namespace.slice(0, depth), ...parts]);
          const homes = this.namespaceHomes.get(key);
          const candidates = [...(homes ?? [])].filter(([module]) => visible.has(module));
          if (!candidates.length) continue;
          href = this.submissionNamespaces.get(key) ?? (candidates.length === 1 ? candidates[0]![1] : undefined);
          break;
        }
      }
      if (href) links.push({ start: token.start, end: token.end, href });
    }
    return links;
  }

  private semanticLinks(module: ModuleSource, namespaceLinks: SourceLink[]): SourceLink[] {
    const candidates = [...module.imports, ...namespaceLinks];
    for (const reference of module.semantic!.constants) {
      const href = this.semanticTarget(reference.module, reference.name);
      if (!href) continue;
      for (const usage of reference.usages) {
        if (usage.start === usage.end) continue;
        candidates.push({ start: usage.start, end: usage.end, href });
      }
    }
    // Lean can report a definition as a use through generated syntax. Keep
    // all definition sites plain, even in that case. Sweep, rather than
    // checking every declaration for every reference.
    const sites = [...module.definitionSites].sort((a, b) => a.start - b.start);
    candidates.sort((a, b) => a.start - b.start || a.end - b.end || a.href.localeCompare(b.href));
    let index = 0;
    const links: SourceLink[] = [];
    for (const candidate of candidates) {
      while (index < sites.length && sites[index]!.end <= candidate.start) index++;
      if (sites[index] && sites[index]!.start < candidate.end) continue;
      const previous = links.at(-1);
      if (previous && previous.end > candidate.start) {
        // Lean records both `T` and `T.{u}` for a universe application.
        // Keep the precise name span; the universe variable stays plain.
        if (previous.href === candidate.href) {
          if (candidate.start <= previous.start && candidate.end >= previous.end) continue;
          if (previous.start <= candidate.start && previous.end >= candidate.end) {
            links[links.length - 1] = candidate;
            continue;
          }
        }
        // A new compiler format must not turn overlapping semantic spans
        // into silently lost links or nested anchors.
        throw new Error(`${module.semantic!.module}: overlapping Lean reference targets`);
      }
      links.push(candidate);
    }
    return links;
  }

  links(conceptId: string): SourceLink[] {
    const cached = this.resolved.get(conceptId);
    if (cached) return cached;
    const module = this.modules.get(conceptId);
    if (!module) return [];
    // Iterative and cycle-safe; don't parse every ancestor again for each page.
    const visible = new Set<string>();
    const pending = [conceptId];
    while (pending.length) {
      const id = pending.pop()!;
      if (visible.has(id)) continue;
      visible.add(id);
      pending.push(...(this.model.conceptHome.get(id)?.concept.imports ?? []));
    }
    const namespaceLinks = this.namespaceLinks(module, visible);
    if (module.semantic) {
      const links = this.semanticLinks(module, namespaceLinks);
      this.resolved.set(conceptId, links);
      return links;
    }
    const links: SourceLink[] = [...namespaceLinks];
    const namespaceSites = new Set(namespaceLinks.map((link) => link.start));
    const destinations = new Map<string, Target[]>();
    const candidates = (parts: readonly string[]) => {
      const key = nameKey(parts);
      let found = destinations.get(key);
      if (!found) {
        found = (this.names.get(key) ?? []).filter((entry) => visible.has(entry.module) &&
          (!entry.private || entry.module === conceptId));
        destinations.set(key, found);
      }
      return found;
    };
    for (const { token, namespace } of module.references) {
      if (namespaceSites.has(token.start)) continue;
      if (!token.name) continue;
      const rooted = token.name[0] === "_root_";
      if (!rooted && module.locals.has(token.name[0]!)) continue;
      const parts = rooted ? token.name.slice(1) : token.name;
      let target: Target | undefined;
      let matched = false;
      // Search the current namespace and its parents, closest first. Never
      // invent a suffix alias from all imports. Keep source order: a later
      // declaration cannot retroactively become a reference's destination.
      for (let depth = rooted ? 0 : namespace.length; depth >= 0; depth--) {
        const found = candidates([...namespace.slice(0, depth), ...parts])
          .filter((entry) => entry.module !== conceptId || entry.offset < token.start);
        if (found.length) {
          matched = true;
          if (found.length === 1) target = found[0];
          break; // Ambiguity in the closest namespace must not fall outward.
        }
      }
      let href = target?.href;
      if (!matched && parts.length > 1 && !candidates(parts).length) {
        const imported = this.model.conceptHome.get(parts.join("."));
        if (imported && visible.has(imported.concept.id) && nameKey(nameParts(imported.concept.id)) === nameKey(parts))
          href = this.page(imported);
      }
      if (href) links.push({ start: token.start, end: token.end, href });
    }
    links.sort((a, b) => a.start - b.start);
    this.resolved.set(conceptId, links);
    return links;
  }
}

/** All URLs are generated from archive destinations, never source-provided
 * URLs. Relative paths also work below /previews/<branch>/. */
export function sourceLinks(model: SiteModel, conceptId: string, rootRel: string): SourceLink[] {
  let index = indexes.get(model);
  if (!index) { index = new SourceLinkIndex(model); indexes.set(model, index); }
  return index.links(conceptId).map((link) => ({ ...link, href: rootRel + link.href }));
}
