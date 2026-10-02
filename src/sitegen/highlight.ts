import { createHighlighter, type Highlighter } from "shiki";
import type { StatementEntry } from "../types.js";
import { attr, esc } from "./html.js";
import { renderDisplayMath, renderInlineMath } from "./math.js";
import { leanDeclarations, nameKey, nameParts, scanLeanSource, type LeanDeclaration, type LeanSource, type SourceRange } from "./lean-source.js";
import type { SourceLink } from "./source-links.js";
import type { SourceHover } from "./lean-code.js";
import { mathlibLinkTitle } from "../mathlib-links.js";

let highlighterPromise: Promise<Highlighter> | undefined;

function highlighter(): Promise<Highlighter> {
  return highlighterPromise ??= createHighlighter({ themes: ["github-light"], langs: ["lean4"] });
}

interface HastNode { type: string; value?: string; tagName?: string; properties?: Record<string, unknown>; children?: HastNode[] }

interface Decoration extends SourceRange { href?: string; hover?: string; hoverLinks?: SourceLink[]; html?: string; contentLine?: number }

function escapedAt(source: string, index: number): boolean {
  let slashes = 0;
  for (let before = index - 1; before >= 0 && source[before] === "\\"; before--) slashes++;
  return slashes % 2 === 1;
}

function closingDollar(source: string, start: number, end: number, display: boolean): number {
  for (let index = start; index < end; index += 1) {
    if (source[index] !== "$" || escapedAt(source, index)) continue;
    if (display ? source.startsWith("$$", index) : source[index + 1] !== "$" && source[index - 1] !== "$")
      return index;
  }
  return -1;
}

/** Decorations are applied to the original highlighted text. No placeholder
 * substitution: preserve syntax colours and never re-interpret generated HTML. */
function commentMath(source: string, comments: SourceRange[]): Decoration[] {
  const matches: Decoration[] = [];
  for (const range of comments) {
    for (let index = range.start; index < range.end;) {
      if (source[index] !== "$" || escapedAt(source, index)) { index++; continue; }
      const display = source[index + 1] === "$";
      const delimiterLength = display ? 2 : 1;
      const closing = closingDollar(source, index + delimiterLength, range.end, display);
      if (closing < 0) { index += delimiterLength; continue; }
      const end = closing + delimiterLength;
      const raw = source.slice(index, end);
      const body = source.slice(index + delimiterLength, closing);
      const math = display ? renderDisplayMath(body.trim(), raw) : renderInlineMath(body.trim(), raw);
      const first = display ? /\S/u.exec(body) : undefined;
      const contentLine = first ? raw.slice(0, first.index + delimiterLength).split("\n").length - 1 : 0;
      matches.push({ start: index, end, contentLine,
        html: `<span class="source-math source-math-${display ? "display" : "inline"}">${math}</span>` });
      index = end;
    }
  }
  return matches;
}

// Besides generated archive pages, permit only validated Lean/Mathlib
// documentation and pinned Mathlib source destinations.
const ARCHIVE_HREF = /^(?:\.\.?\/)*[a-zA-Z0-9_%.'-]+\/[a-zA-Z0-9_%.'-]+\.html(?:#[a-zA-Z0-9_%.'-]+)?$/u;

function decorationsByLine(source: string, links: readonly SourceLink[], comments: SourceRange[], hovers: readonly SourceHover[], typeLinks?: SourceOptions["typeLinks"]): Decoration[][] {
  const lines = source.split("\n");
  const offsets = [0];
  for (const line of lines) offsets.push(offsets.at(-1)! + line.length + 1);
  const result: Decoration[][] = lines.map(() => []);
  const identifiers: Decoration[] = links.filter((link) =>
    Number.isInteger(link.start) && Number.isInteger(link.end) && link.start >= 0 &&
    link.end > link.start && link.end <= source.length && (ARCHIVE_HREF.test(link.href) || mathlibLinkTitle(link.href)),
  ).map(link => ({ ...link }));
  const identifierRanges = new Map(identifiers.map(link => [`${link.start}:${link.end}`, link]));
  for (const hover of hovers) {
    if (!Number.isInteger(hover.start) || !Number.isInteger(hover.end) || hover.start < 0 || hover.end <= hover.start ||
        hover.end > source.length || typeof hover.text !== "string") continue;
    const linked = identifierRanges.get(`${hover.start}:${hover.end}`);
    const hoverLinks = [...(typeLinks?.(hover.text) ?? [])];
    // The term's own name stays plain: its source occurrence is the link.
    const first = scanLeanSource(hover.text).tokens[0];
    const safeLinks = hoverLinks.filter(link => Number.isInteger(link.start) && Number.isInteger(link.end) &&
      link.start >= (first?.end ?? 0) && link.end > link.start && link.end <= hover.text.length &&
      (ARCHIVE_HREF.test(link.href) || mathlibLinkTitle(link.href)))
      .map(link => ({ ...link, title: mathlibLinkTitle(link.href) }));
    if (linked) { linked.hover = hover.text; linked.hoverLinks = safeLinks; }
    else identifiers.push({ start: hover.start, end: hover.end, hover: hover.text, hoverLinks: safeLinks });
  }
  const decorations: Decoration[] = [...commentMath(source, comments), ...identifiers].sort((a, b) => a.start - b.start);
  let line = 0;
  let previousEnd = 0;
  for (const decoration of decorations) {
    if (decoration.start < previousEnd) continue;
    previousEnd = decoration.end;
    while (offsets[line + 1]! <= decoration.start) line++;
    const contentLine = line + (decoration.contentLine ?? 0);
    for (let row = line; row < lines.length && offsets[row]! < decoration.end; row++) {
      result[row]!.push({
        start: Math.max(0, decoration.start - offsets[row]!),
        end: Math.min(lines[row]!.length, decoration.end - offsets[row]!),
        href: decoration.href,
        hover: decoration.hover,
        hoverLinks: decoration.hoverLinks,
        html: row === contentLine ? decoration.html : "",
      });
    }
  }
  return result;
}

function openingTag(node: HastNode): string {
  const properties = Object.entries(node.properties ?? {}).map(([key, value]) => {
    const name = key === "className" ? "class" : key;
    const rendered = Array.isArray(value) ? value.join(" ") : String(value);
    return ` ${name}="${esc(rendered)}"`;
  }).join("");
  return `<${node.tagName}${properties}>`;
}

/** Walk highlighted fragments once, splitting only at decoration boundaries.
 * One identifier gets one anchor even when Shiki colours its parts differently. */
function renderDecoratedLine(nodes: HastNode[], decorations: Decoration[]): string {
  if (!decorations.length) return nodes.map(renderNode).join("");
  const fragments: { text: string; open: string; close: string }[] = [];
  const visit = (node: HastNode, open = "", close = "") => {
    if (node.type === "text") {
      if (node.value) fragments.push({ text: node.value, open, close });
    } else if (node.type === "element") {
      for (const child of node.children ?? []) visit(child, open + openingTag(node), `</${node.tagName}>` + close);
    } else for (const child of node.children ?? []) visit(child, open, close);
  };
  nodes.forEach((node) => visit(node));
  let fragment = 0;
  let consumed = 0;
  let offset = 0;
  const take = (end: number): string => {
    const html: string[] = [];
    while (fragment < fragments.length && offset < end) {
      const current = fragments[fragment]!;
      const count = Math.min(current.text.length - consumed, end - offset);
      html.push(current.open, esc(current.text.slice(consumed, consumed + count)), current.close);
      consumed += count;
      offset += count;
      if (consumed === current.text.length) { fragment++; consumed = 0; }
    }
    return html.join("");
  };
  const html: string[] = [];
  for (const decoration of decorations) {
    html.push(take(decoration.start));
    const content = take(decoration.end);
    const destination = decoration.href ? mathlibLinkTitle(decoration.href) : undefined;
    const title = decoration.hover ? undefined : destination;
    const hover = decoration.hover ? ` data-lean-type="${attr(decoration.hover)}" aria-haspopup="dialog"${decoration.hoverLinks?.length ? ` data-lean-type-links="${attr(JSON.stringify(decoration.hoverLinks))}"` : ""}` : "";
    html.push(decoration.href
      ? `<a class="lean-identifier-link" href="${attr(decoration.href)}"${hover}${decoration.hover && destination ? ` data-lean-destination="${attr(destination)}"` : ""}${title ? ` title="${attr(title)}"` : ""}>${content}</a>`
      : decoration.hover ? `<span class="lean-typed-identifier" role="button" tabindex="0"${hover}>${content}</span>`
      : decoration.html ?? "");
  }
  html.push(take(Infinity));
  return html.join("");
}

function renderNode(node: HastNode): string {
  if (node.type === "text") return esc(node.value ?? "");
  if (node.type !== "element") return (node.children ?? []).map(renderNode).join("");
  return `${openingTag(node)}${(node.children ?? []).map(renderNode).join("")}</${node.tagName}>`;
}

function lineNodes(root: HastNode): HastNode[] {
  const found: HastNode[] = [];
  const visit = (node: HastNode) => {
    const classes = node.properties?.className ?? node.properties?.class;
    if (node.type === "element" && node.tagName === "span" &&
        (Array.isArray(classes) ? classes.includes("line") : classes === "line")) found.push(node);
    else node.children?.forEach(visit);
  };
  visit(root);
  return found;
}

interface SnippetOptions {
  startLine?: number;
  accentLines?: readonly number[];
}

/** A compact, GitHub-light Lean excerpt for editorial surfaces. Unlike the
 * line-numbered concept source table, this deliberately carries no statement
 * anchors or proof-status tinting. */
export async function highlightSnippet(source: string, options: SnippetOptions = {}): Promise<string> {
  const startLine = options.startLine ?? 1;
  const accentLines = new Set(options.accentLines ?? []);
  const lineHtml = (content: string, index: number) => {
    const sourceLine = index + 1;
    const classes = `landing-demo-code-line${accentLines.has(sourceLine) ? " landing-demo-code-line-accent" : ""}`;
    return `<span class="${classes}" data-line="${startLine + index}">${content || " "}</span>`;
  };
  try {
    const hast = (await highlighter()).codeToHast(source.trim(), {
      lang: "lean4",
      theme: "github-light",
    }) as HastNode;
    return lineNodes(hast).map((line, index) =>
      lineHtml((line.children ?? []).map(renderNode).join(""), index)
    ).join("\n");
  } catch {
    return source.trim().split("\n").map((line, index) =>
      lineHtml(esc(line), index)
    ).join("\n");
  }
}

function lineStatus(line: number, statements: StatementEntry[], proven: Set<string>): string {
  const statement = statements.find((s) => s.startLine !== undefined && s.endLine !== undefined && line >= s.startLine && line <= s.endLine);
  return statement ? ` statement-line ${proven.has(statement.id) ? "line-proven" : "line-open"}` : "";
}

function statementAnchors(line: number, statements: StatementEntry[]): string {
  return statements
    .filter((statement) => statement.startLine === line)
    .map((statement) => `<span class="statement-anchor" id="s-${esc(statement.id)}"></span>`)
    .join("");
}

export interface SourceOptions {
  /** Drop the leading module docstring (`/-! … -/`) behind one elided row;
   * the line numbers of what remains stay the file's. */
  omitModuleDoc?: boolean;
  /** Emit `id`s and links on the rows (the concept page); off where the
   * same source may appear more than once on a page (the paper cards). */
  anchors?: boolean;
  /** Verified archive destinations at offsets in the original source. */
  links?: readonly SourceLink[];
  hovers?: readonly SourceHover[];
  /** Validated links within a compiler type, using this page's relative root. */
  typeLinks?: (text: string) => readonly SourceLink[];
}

/** The 1-based line range of the module docstring — the first `/-!` block
 * ahead of any declaration — or undefined without one. */
export function moduleDocRange(source: string): [number, number] | undefined {
  const lines = source.split("\n");
  let start = -1;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!.trim();
    if (line.startsWith("/-!")) { start = i; break; }
    if (line === "" || line.startsWith("import ") || line.startsWith("--")) continue;
    return undefined;
  }
  if (start < 0) return undefined;
  for (let i = start; i < lines.length; i++) if (lines[i]!.includes("-/")) return [start + 1, i + 1];
  return undefined;
}

/** Suppress redundant type bubbles at annotated bindings and declaration
 * names, including grouped binders and return types after parameter lists. */
function explicitTypeSites({ tokens }: LeanSource, declarations: LeanDeclaration[]): Set<string> {
  const sites = new Set<string>();
  const mark = (token: SourceRange) => sites.add(`${token.start}:${token.end}`);
  const positions = new Map(tokens.map((token, index) => [token.start, index]));
  const closes = new Map<number, number>();
  const stack: number[] = [];
  const opening = new Set(["(", "[", "{", "⦃", "⟨"]);
  const closing = new Set([")", "]", "}", "⦄", "⟩"]);
  const bindingCommands = new Set(["def", "abbrev", "opaque", "constant", "axiom", "theorem", "lemma",
    "variable", "variables", "let", "letI", "let'", "letI'", "have", "haveI", "suffices", "fun"]);
  const annotation = (index: number) => tokens[index]?.text === ":" && tokens[index + 1]?.text !== "=";
  for (let index = 0; index < tokens.length; index++) {
    const token = tokens[index]!;
    if (opening.has(token.text)) stack.push(index);
    else if (closing.has(token.text)) {
      const start = stack.pop();
      if (start !== undefined) closes.set(start, index);
    }
    if (annotation(index)) {
      // `x y : T` annotates both names. Only a binder introducer allows the
      // name list to span lines; otherwise a preceding field's type could
      // be mistaken for another name in the next field declaration.
      let before = index - 1;
      while (before >= 0 && tokens[before]!.name && !bindingCommands.has(tokens[before]!.text)) before--;
      const multiline = ["(", "[", "{", "⦃", "∀", "∃", "fun", "variable", "variables"].includes(tokens[before]?.text ?? "");
      for (let name = before + 1; name < index; name++)
        if (multiline || tokens[name]!.line === tokens[index - 1]!.line) mark(tokens[name]!);
    }
  }
  const names = new Set(declarations.map(declaration => positions.get(declaration.token.start)!));
  for (let index = 1; index < tokens.length; index++)
    if (["let", "letI", "let'", "letI'", "have", "haveI", "suffices", "instance"].includes(tokens[index - 1]!.text) && tokens[index]!.name)
      names.add(index);
  for (const index of names) {
    if (["axiom", "theorem", "lemma"].includes(tokens[index - 1]?.text ?? "")) mark(tokens[index]!);
    let next = index + 1;
    // An explicit universe list precedes a declaration's parameters.
    if (tokens[next]?.text === "." && tokens[next + 1]?.text === "{") next++;
    while (closes.has(next)) next = closes.get(next)! + 1;
    if (annotation(next)) mark(tokens[index]!);
  }
  return sites;
}

export async function highlightSource(
  source: string,
  statements: StatementEntry[] = [],
  proven = new Set<string>(),
  options: SourceOptions = {},
): Promise<string> {
  const anchors = options.anchors ?? true;
  const elided = options.omitModuleDoc ? moduleDocRange(source) : undefined;
  const parsed = scanLeanSource(source);
  const declarations = leanDeclarations(parsed);
  const annotated = explicitTypeSites(parsed, declarations);
  const hovers = (options.hovers ?? []).filter(hover => !annotated.has(`${hover.start}:${hover.end}`));
  const decorations = decorationsByLine(source, options.links ?? [], parsed.comments, hovers, options.typeLinks);
  // Keep stable statement IDs, but place them at their complete comment
  // preamble. Archive ranges may begin after leading ordinary line comments.
  const starts = anchors && statements.length
    ? new Map(declarations.map((d) => [nameKey(d.name), d.startLine]))
    : new Map<string, number>();
  const anchorStatements = statements.map((statement) => ({
    ...statement,
    startLine: starts.get(nameKey(nameParts(statement.id))) ?? statement.startLine,
  }));
  const commentLines = new Set<number>();
  for (const comment of parsed.comments) {
    const first = source.slice(0, comment.start).split("\n").length;
    const last = source.slice(0, comment.end).split("\n").length;
    for (let line = first; line <= last; line++) commentLines.add(line);
  }
  const row = (n: number, highlighted: string) => {
    if (elided && n >= elided[0] && n <= elided[1]) {
      return n === elided[0]
        ? `<tr class="line-elided"><td class="line-num"></td><td class="line-code">… module docstring, ${elided[1] - elided[0] + 1} lines</td></tr>`
        : "";
    }
    const id = anchors ? ` id="L${n}"` : "";
    const num = anchors ? `<a href="#L${n}">${n}</a>` : String(n);
    const anchorSpans = anchors ? statementAnchors(n, anchorStatements) : "";
    const classes = [lineStatus(n, statements, proven).trim(), anchors && commentLines.has(n) ? "line-comment" : ""].filter(Boolean).join(" ");
    return `<tr${id} class="${classes}"><td class="line-num">${num}</td><td class="line-code">${anchorSpans}${highlighted || " "}</td></tr>`;
  };
  let rows: string[];
  try {
    const hast = (await highlighter()).codeToHast(source, { lang: "lean4", theme: "github-light" }) as HastNode;
    rows = lineNodes(hast).map((line, index) =>
      row(index + 1, renderDecoratedLine(line.children ?? [], decorations[index] ?? [])));
  } catch {
    rows = source.split("\n").map((line, index) =>
      row(index + 1, renderDecoratedLine([{ type: "text", value: line }], decorations[index] ?? [])));
  }
  return rows.filter(Boolean).join("\n");
}
