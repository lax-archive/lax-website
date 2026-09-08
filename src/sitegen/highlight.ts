import { createHighlighter, type Highlighter } from "shiki";
import type { StatementEntry } from "../types.js";
import { attr, esc } from "./html.js";
import { renderDisplayMath, renderInlineMath } from "./math.js";

let highlighterPromise: Promise<Highlighter> | undefined;

function highlighter(): Promise<Highlighter> {
  return highlighterPromise ??= createHighlighter({ themes: ["github-light"], langs: ["lean4"] });
}

interface HastNode { type: string; value?: string; tagName?: string; properties?: Record<string, unknown>; children?: HastNode[] }

interface SourceRange { start: number; end: number }

interface SourceMathReplacement {
  placeholder: string;
  html: string;
}

interface SourceLinkReplacement {
  placeholder: string;
  identifier: string;
  href: string;
}

export type SourceIdentifierHref = (identifier: string) => string | undefined;

const LEAN_IDENTIFIER = /^[\p{L}_][\p{L}\p{N}\p{M}_']*(?:\.[\p{L}_][\p{L}\p{N}\p{M}_']*)*/u;
const IDENTIFIER_START = /[\p{L}_]/u;
const IDENTIFIER_BOUNDARY = /[\p{L}\p{N}\p{M}_'.]/u;
const LEAN_DECLARATION = /^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*(?:def|abbrev|structure|class|inductive|theorem|lemma|axiom|opaque|constant)[ \t]+([\p{L}_][\p{L}\p{N}\p{M}_']*(?:\.[\p{L}_][\p{L}\p{N}\p{M}_']*)*)/gmu;

function escapedAt(source: string, index: number): boolean {
  let slashes = 0;
  for (let before = index - 1; before >= 0 && source[before] === "\\"; before -= 1)
    slashes += 1;
  return slashes % 2 === 1;
}

/** Locate Lean comments without asking the highlighter to expose private
 * TextMate scopes. Block comments may nest; strings and quoted identifiers
 * are skipped so comment-looking text inside them remains ordinary code. */
function commentRanges(source: string): SourceRange[] {
  const ranges: SourceRange[] = [];
  for (let index = 0; index < source.length;) {
    if (source[index] === "\"") {
      index += 1;
      while (index < source.length) {
        if (source[index] === "\\") index += 2;
        else if (source[index++] === "\"") break;
      }
      continue;
    }
    if (source[index] === "«") {
      const closing = source.indexOf("»", index + 1);
      index = closing < 0 ? source.length : closing + 1;
      continue;
    }
    if (source.startsWith("--", index)) {
      const closing = source.indexOf("\n", index + 2);
      ranges.push({ start: index, end: closing < 0 ? source.length : closing });
      index = closing < 0 ? source.length : closing + 1;
      continue;
    }
    if (source.startsWith("/-", index)) {
      const start = index;
      let depth = 1;
      index += 2;
      while (index < source.length && depth > 0) {
        if (source.startsWith("/-", index)) { depth += 1; index += 2; }
        else if (source.startsWith("-/", index)) { depth -= 1; index += 2; }
        else index += 1;
      }
      ranges.push({ start, end: index });
      continue;
    }
    index += 1;
  }
  return ranges;
}

/** Extract ordinary named Lean declarations while ignoring comments, strings,
 * and quoted identifiers. These names let a concept source link unqualified
 * definitions imported from other archive modules without pretending that
 * arbitrary identifiers are globally unique. */
export function leanDeclarationNames(source: string): string[] {
  const masked = source.split("");
  const blank = (start: number, end: number) => {
    for (let index = start; index < end; index++)
      if (masked[index] !== "\n" && masked[index] !== "\r") masked[index] = " ";
  };

  for (let index = 0; index < source.length;) {
    const start = index;
    if (source[index] === "\"") {
      index += 1;
      while (index < source.length) {
        if (source[index] === "\\") index += 2;
        else if (source[index++] === "\"") break;
      }
      blank(start, Math.min(index, source.length));
      continue;
    }
    if (source[index] === "«") {
      const closing = source.indexOf("»", index + 1);
      index = closing < 0 ? source.length : closing + 1;
      blank(start, index);
      continue;
    }
    if (source.startsWith("--", index)) {
      const closing = source.indexOf("\n", index + 2);
      index = closing < 0 ? source.length : closing;
      blank(start, index);
      continue;
    }
    if (source.startsWith("/-", index)) {
      let depth = 1;
      index += 2;
      while (index < source.length && depth > 0) {
        if (source.startsWith("/-", index)) { depth += 1; index += 2; }
        else if (source.startsWith("-/", index)) { depth -= 1; index += 2; }
        else index += 1;
      }
      blank(start, index);
      continue;
    }
    index += 1;
  }

  const names: string[] = [];
  for (const match of masked.join("").matchAll(LEAN_DECLARATION)) names.push(match[1]!);
  return names;
}

function closingDollar(source: string, start: number, end: number, display: boolean): number {
  for (let index = start; index < end; index += 1) {
    if (source[index] !== "$" || escapedAt(source, index)) continue;
    if (display ? source.startsWith("$$", index) : source[index + 1] !== "$" && source[index - 1] !== "$")
      return index;
  }
  return -1;
}

/** Keep the exact number of source rows while replacing a delimited formula
 * with one highlighter-safe token. A multiline display is restored on its
 * first content row; its delimiter rows remain empty but addressable. */
function mathPlaceholder(raw: string, placeholder: string, display: boolean): string {
  const lines = raw.split("\n");
  if (lines.length === 1) return placeholder;
  let targetLine = 0;
  if (display) {
    const body = raw.slice(2, -2);
    const content = /\S/.exec(body);
    if (content) targetLine = (raw.slice(0, content.index + 2).match(/\n/g) ?? []).length;
  }
  return lines.map((_, index) => index === targetLine ? placeholder : "").join("\n");
}

/** Mask comment math before Shiki sees it, then restore safe KaTeX HTML after
 * highlighting. This prevents Lean strings or syntax containing `$` from
 * being interpreted as prose while preserving source line anchors exactly. */
function maskCommentMath(source: string): { masked: string; replacements: SourceMathReplacement[] } {
  let prefix = "LAXSOURCEMATHTOKEN";
  while (source.includes(prefix)) prefix += "X";
  const matches: { start: number; end: number; replacement: string; rendered: SourceMathReplacement }[] = [];

  for (const range of commentRanges(source)) {
    for (let index = range.start; index < range.end;) {
      if (source[index] !== "$" || escapedAt(source, index)) { index += 1; continue; }
      const display = source[index + 1] === "$";
      const delimiterLength = display ? 2 : 1;
      const closing = closingDollar(source, index + delimiterLength, range.end, display);
      if (closing < 0) { index += delimiterLength; continue; }
      const end = closing + delimiterLength;
      const raw = source.slice(index, end);
      const text = source.slice(index + delimiterLength, closing).trim();
      const placeholder = `${prefix}${matches.length}END`;
      const math = display ? renderDisplayMath(text, raw) : renderInlineMath(text, raw);
      matches.push({
        start: index,
        end,
        replacement: mathPlaceholder(raw, placeholder, display),
        rendered: {
          placeholder,
          html: `<span class="source-math source-math-${display ? "display" : "inline"}">${math}</span>`,
        },
      });
      index = end;
    }
  }

  let masked = source;
  for (const match of [...matches].reverse())
    masked = masked.slice(0, match.start) + match.replacement + masked.slice(match.end);
  return { masked, replacements: matches.map((match) => match.rendered) };
}

function restoreCommentMath(html: string, replacements: SourceMathReplacement[]): string {
  for (const replacement of replacements)
    html = html.replace(replacement.placeholder, replacement.html);
  return html;
}

/** Replace resolvable archive identifiers in actual Lean code with inert
 * tokens before highlighting. Comments, strings, and quoted identifiers are
 * deliberately skipped: their contents are prose or data, not references in
 * the Lean syntax tree. */
function maskSourceLinks(source: string, hrefForIdentifier?: SourceIdentifierHref): {
  masked: string;
  replacements: SourceLinkReplacement[];
} {
  if (!hrefForIdentifier) return { masked: source, replacements: [] };

  let prefix = "LAXSOURCELINKTOKEN";
  while (source.includes(prefix)) prefix += "X";
  const matches: { start: number; end: number; replacement: SourceLinkReplacement }[] = [];

  for (let index = 0; index < source.length;) {
    if (source[index] === "\"") {
      index += 1;
      while (index < source.length) {
        if (source[index] === "\\") index += 2;
        else if (source[index++] === "\"") break;
      }
      continue;
    }
    if (source[index] === "«") {
      const closing = source.indexOf("»", index + 1);
      index = closing < 0 ? source.length : closing + 1;
      continue;
    }
    if (source.startsWith("--", index)) {
      const closing = source.indexOf("\n", index + 2);
      index = closing < 0 ? source.length : closing + 1;
      continue;
    }
    if (source.startsWith("/-", index)) {
      let depth = 1;
      index += 2;
      while (index < source.length && depth > 0) {
        if (source.startsWith("/-", index)) { depth += 1; index += 2; }
        else if (source.startsWith("-/", index)) { depth -= 1; index += 2; }
        else index += 1;
      }
      continue;
    }

    const previous = source[index - 1];
    if (!IDENTIFIER_START.test(source[index]!) || (previous !== undefined && IDENTIFIER_BOUNDARY.test(previous))) {
      index += 1;
      continue;
    }
    const identifier = LEAN_IDENTIFIER.exec(source.slice(index))?.[0];
    const next = identifier === undefined ? undefined : source[index + identifier.length];
    if (!identifier || (next !== undefined && IDENTIFIER_BOUNDARY.test(next))) {
      index += 1;
      continue;
    }
    const href = hrefForIdentifier(identifier);
    if (href) {
      matches.push({
        start: index,
        end: index + identifier.length,
        replacement: { placeholder: `${prefix}${matches.length}END`, identifier, href },
      });
    }
    index += identifier.length;
  }

  let masked = source;
  for (const match of [...matches].reverse())
    masked = masked.slice(0, match.start) + match.replacement.placeholder + masked.slice(match.end);
  return { masked, replacements: matches.map((match) => match.replacement) };
}

function restoreSourceLinks(html: string, replacements: SourceLinkReplacement[]): string {
  for (const replacement of replacements) {
    const link = `<a class="lean-identifier-link" href="${attr(replacement.href)}">${esc(replacement.identifier)}</a>`;
    html = html.replace(replacement.placeholder, () => link);
  }
  return html;
}

function renderNode(node: HastNode): string {
  if (node.type === "text") return esc(node.value ?? "");
  if (node.type !== "element") return (node.children ?? []).map(renderNode).join("");
  const properties = Object.entries(node.properties ?? {}).map(([key, value]) => {
    const name = key === "className" ? "class" : key;
    const rendered = Array.isArray(value) ? value.join(" ") : String(value);
    return ` ${name}="${esc(rendered)}"`;
  }).join("");
  return `<${node.tagName}${properties}>${(node.children ?? []).map(renderNode).join("")}</${node.tagName}>`;
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
  /** Turn archive-qualified Lean names into links when the destination is
   * known to the site model. */
  hrefForIdentifier?: SourceIdentifierHref;
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

export async function highlightSource(
  source: string,
  statements: StatementEntry[] = [],
  proven = new Set<string>(),
  options: SourceOptions = {},
): Promise<string> {
  const anchors = options.anchors ?? true;
  const elided = options.omitModuleDoc ? moduleDocRange(source) : undefined;
  const math = maskCommentMath(source);
  const links = maskSourceLinks(math.masked, options.hrefForIdentifier);
  const row = (n: number, highlighted: string) => {
    if (elided && n >= elided[0] && n <= elided[1]) {
      return n === elided[0]
        ? `<tr class="line-elided"><td class="line-num"></td><td class="line-code">… module docstring, ${elided[1] - elided[0] + 1} lines</td></tr>`
        : "";
    }
    const id = anchors ? ` id="L${n}"` : "";
    const num = anchors ? `<a href="#L${n}">${n}</a>` : String(n);
    const anchorSpans = anchors ? statementAnchors(n, statements) : "";
    return `<tr${id} class="${lineStatus(n, statements, proven).trim()}"><td class="line-num">${num}</td><td class="line-code">${anchorSpans}${highlighted || " "}</td></tr>`;
  };
  let rows: string[];
  try {
    const hast = (await highlighter()).codeToHast(links.masked, { lang: "lean4", theme: "github-light" }) as HastNode;
    rows = lineNodes(hast).map((line, index) =>
      row(index + 1, restoreCommentMath(
        restoreSourceLinks((line.children ?? []).map(renderNode).join(""), links.replacements),
        math.replacements,
      )));
  } catch {
    rows = links.masked.split("\n").map((line, index) => row(index + 1, restoreCommentMath(
        restoreSourceLinks(esc(line), links.replacements),
        math.replacements,
      )));
  }
  return rows.filter(Boolean).join("\n");
}
