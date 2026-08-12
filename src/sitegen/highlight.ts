import { createHighlighter, type Highlighter } from "shiki";
import type { StatementEntry } from "../types.js";
import { attr, esc } from "./html.js";

let highlighterPromise: Promise<Highlighter> | undefined;

function highlighter(): Promise<Highlighter> {
  return highlighterPromise ??= createHighlighter({ themes: ["github-light"], langs: ["lean4"] });
}

interface HastNode { type: string; value?: string; tagName?: string; properties?: Record<string, unknown>; children?: HastNode[] }

export interface StatementProofLink { id: string; href: string }

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

/** Build output includes a statement's leading doc comment in its source
 * range. Put proof actions on the declaration itself, rather than beside the
 * first documentation line. */
function statementDeclarationLine(sourceLines: string[], statement: StatementEntry): number | undefined {
  if (statement.startLine === undefined || statement.endLine === undefined) return statement.startLine;
  for (let line = statement.startLine; line <= statement.endLine; line++) {
    if (/^\s*(?:axiom|theorem|lemma)\b/.test(sourceLines[line - 1] ?? "")) return line;
  }
  return statement.startLine;
}

function statementProofActions(
  line: number,
  sourceLines: string[],
  statements: StatementEntry[],
  proofLinks: ReadonlyMap<string, readonly StatementProofLink[]>,
): string {
  const links = statements.flatMap((statement) =>
    statementDeclarationLine(sourceLines, statement) === line ? proofLinks.get(statement.id) ?? [] : []);
  if (links.length === 0) return '<td class="statement-actions"></td>';
  return `<td class="statement-actions"><span class="statement-proof-links">${links.map((link, index) => {
    const label = links.length === 1 ? "Go to Proof" : `Go to Proof ${index + 1}`;
    return `<a class="statement-proof-button" href="${attr(link.href)}" aria-label="${attr(`Open proof ${link.id}`)}" title="${attr(link.id)}"><span class="statement-proof-mark" aria-hidden="true">⊢</span><span class="statement-proof-label">${label}</span><span class="statement-proof-arrow" aria-hidden="true">→</span></a>`;
  }).join("")}</span></td>`;
}

export async function highlightSource(
  source: string,
  statements: StatementEntry[] = [],
  proven = new Set<string>(),
  proofLinks: ReadonlyMap<string, readonly StatementProofLink[]> = new Map(),
): Promise<string> {
  const sourceLines = source.split("\n");
  const actions = (line: number) => proofLinks.size
    ? statementProofActions(line, sourceLines, statements, proofLinks)
    : "";
  try {
    const hast = (await highlighter()).codeToHast(source, { lang: "lean4", theme: "github-light" }) as HastNode;
    const lines = lineNodes(hast);
    return lines.map((line, index) => {
      const n = index + 1;
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${(line.children ?? []).map(renderNode).join("") || " "}</td>${actions(n)}</tr>`;
    }).join("\n");
  } catch {
    return sourceLines.map((line, index) => {
      const n = index + 1;
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${esc(line) || " "}</td>${actions(n)}</tr>`;
    }).join("\n");
  }
}
