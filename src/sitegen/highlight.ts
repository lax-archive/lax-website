import { createHighlighter, type Highlighter } from "shiki";
import type { StatementEntry } from "../types.js";
import { esc } from "./html.js";
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

/** A compact, GitHub-light Lean excerpt for editorial surfaces. Unlike the
 * line-numbered concept source table, this deliberately carries no statement
 * anchors or proof-status tinting. */
export async function highlightSnippet(source: string): Promise<string> {
  try {
    const hast = (await highlighter()).codeToHast(source.trim(), {
      lang: "lean4",
      theme: "github-light",
    }) as HastNode;
    return lineNodes(hast).map((line, index) =>
      `<span class="landing-demo-code-line" data-line="${index + 1}">${(line.children ?? []).map(renderNode).join("") || " "}</span>`
    ).join("\n");
  } catch {
    return source.trim().split("\n").map((line, index) =>
      `<span class="landing-demo-code-line" data-line="${index + 1}">${esc(line) || " "}</span>`
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

export async function highlightSource(source: string, statements: StatementEntry[] = [], proven = new Set<string>()): Promise<string> {
  const math = maskCommentMath(source);
  try {
    const hast = (await highlighter()).codeToHast(math.masked, { lang: "lean4", theme: "github-light" }) as HastNode;
    const lines = lineNodes(hast);
    return lines.map((line, index) => {
      const n = index + 1;
      const highlighted = restoreCommentMath((line.children ?? []).map(renderNode).join(""), math.replacements);
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${highlighted || " "}</td></tr>`;
    }).join("\n");
  } catch {
    return math.masked.split("\n").map((line, index) => {
      const n = index + 1;
      const highlighted = restoreCommentMath(esc(line), math.replacements);
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${highlighted || " "}</td></tr>`;
    }).join("\n");
  }
}
