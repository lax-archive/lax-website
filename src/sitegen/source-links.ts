import { leanDeclarations, nameKey, nameParts, scanLeanSource, type LeanSource, type LeanToken, type SourceRange } from "./lean-source.js";
import type { LocatedConcept, SiteModel } from "./model.js";

export interface SourceLink extends SourceRange { href: string }
interface Target { module: string; href: string }
interface ModuleSource { tokens: LeanToken[]; declarations: Map<number, Target>; locals: Set<string> }

/** Even dotted syntax can be local: `let N.value := ...; N.value`, or a
 * projection through a binder named N. Suppress these spellings throughout
 * the file; narrowing their scopes would require elaborated references. */
function possibleLocals(source: LeanSource, declarations: Map<number, Target>): Set<string> {
  const locals = new Set<string>();
  const bind = (index: number) => {
    const token = source.tokens[index]!;
    if (token.name && !declarations.has(token.start)) locals.add(token.name[0]!);
  };
  let header = false;
  let depth = 0;
  for (let i = 0; i < source.tokens.length; i++) {
    const token = source.tokens[i]!;
    if (["let", "have", "suffices", "obtain", "fun", "∀", "∃", "λ"].includes(token.text)) {
      header = true;
      depth = 0;
      continue;
    }
    if (token.text === ":" || (token.text === "=" && source.tokens[i + 1]?.text === ">")) {
      for (let before = i - 1; before >= 0 && source.tokens[before]!.name; before--) {
        const previous = source.tokens[before]!;
        if (declarations.has(previous.start) || ["example", "instance", "variable", "variables"].includes(previous.text)) break;
        bind(before);
      }
      header = false;
    }
    if (!header) continue;
    if (["(", "[", "{", "⦃"].includes(token.text)) depth++;
    if ([")", "]", "}", "⦄"].includes(token.text)) depth--;
    if ((token.text === "," && depth === 0) || token.text === "in" || token.text === "=") header = false;
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
      const declarations = new Map<number, Target>();
      const statements = new Map(concept.statements.map((s) => [nameKey(nameParts(s.id)), s]));
      for (const declaration of leanDeclarations(source)) {
        const key = nameKey(declaration.name);
        const statement = statements.get(key);
        const fragment = statement?.startLine !== undefined ? `s-${statement.id}` : `L${declaration.token.line}`;
        const target = { module: concept.id, href: `${this.page(located)}#${encodeURIComponent(fragment)}` };
        declarations.set(declaration.token.start, target);
        if (declaration.private) continue; // Lean gives private globals generated names.
        const candidates = this.names.get(key) ?? [];
        candidates.push(target);
        this.names.set(key, candidates);
      }
      this.modules.set(concept.id, {
        tokens: source.tokens.filter((token) => declarations.has(token.start) || (token.name?.length ?? 0) > 1),
        declarations, locals: possibleLocals(source, declarations),
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
    const destinations = new Map<string, Target | undefined>();
    for (const token of module.tokens) {
      if (!token.name) continue;
      let target = module.declarations.get(token.start);
      // A bare spelling is not evidence of an imported reference. Binders,
      // open namespaces, dot notation and macros require Lean's elaborator.
      // Link declaration sites and exact qualified names, never suffix guesses.
      if (!target && token.name.length > 1 && !module.locals.has(token.name[0]!)) {
        const parts = token.name[0] === "_root_" ? token.name.slice(1) : token.name;
        const key = nameKey(parts);
        if (destinations.has(key)) target = destinations.get(key);
        else {
          const candidates = (this.names.get(key) ?? []).filter((entry) => visible.has(entry.module));
          if (candidates.length === 1) target = candidates[0];
          else if (!candidates.length) {
            const imported = this.model.conceptHome.get(parts.join("."));
            if (imported && visible.has(imported.concept.id) && nameKey(nameParts(imported.concept.id)) === key)
              target = { module: imported.concept.id, href: this.page(imported) };
          }
          destinations.set(key, target);
        }
      }
      if (target) links.push({ start: token.start, end: token.end, href: target.href });
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
