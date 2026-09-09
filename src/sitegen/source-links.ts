import { leanDeclarations, nameKey, nameParts, scanLeanSource, type LeanSource, type LeanToken, type SourceRange } from "./lean-source.js";
import type { LocatedConcept, SiteModel } from "./model.js";

export interface SourceLink extends SourceRange { href: string }
interface Target { module: string; href: string; offset: number; private: boolean }
interface Reference { token: LeanToken; namespace: readonly string[] }
interface ModuleSource { references: Reference[]; locals: Set<string> }

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
  private readonly resolved = new Map<string, SourceLink[]>();

  constructor(private readonly model: SiteModel) {
    for (const located of model.conceptHome.values()) {
      const { concept } = located;
      const source = scanLeanSource(concept.sourceText);
      const references: Reference[] = [];
      const inventory = leanDeclarations(source, (token, namespace) => references.push({ token, namespace }));
      const declarations = new Set(inventory.map((declaration) => declaration.token.start));
      const statements = new Map(concept.statements.map((s) => [nameKey(nameParts(s.id)), s]));
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
      this.modules.set(concept.id, {
        references, locals: possibleLocals(source, declarations),
      });
    }
  }

  private page({ output, concept }: LocatedConcept): string {
    return `${encodeURIComponent(output.id)}/${encodeURIComponent(concept.id)}.html`;
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
    const links: SourceLink[] = [];
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
