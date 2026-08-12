import { createHighlighter, type Highlighter } from "shiki";
import type { StatementEntry } from "../types.js";
import { esc } from "./html.js";

let highlighterPromise: Promise<Highlighter> | undefined;

function highlighter(): Promise<Highlighter> {
  return highlighterPromise ??= createHighlighter({ themes: ["github-light"], langs: ["lean4"] });
}

interface HastNode { type: string; value?: string; tagName?: string; properties?: Record<string, unknown>; children?: HastNode[] }

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

export async function highlightSource(source: string, statements: StatementEntry[] = [], proven = new Set<string>()): Promise<string> {
  try {
    const hast = (await highlighter()).codeToHast(source, { lang: "lean4", theme: "github-light" }) as HastNode;
    const lines = lineNodes(hast);
    return lines.map((line, index) => {
      const n = index + 1;
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${(line.children ?? []).map(renderNode).join("") || " "}</td></tr>`;
    }).join("\n");
  } catch {
    return source.split("\n").map((line, index) => {
      const n = index + 1;
      return `<tr id="L${n}" class="${lineStatus(n, statements, proven).trim()}"><td class="line-num"><a href="#L${n}">${n}</a></td><td class="line-code">${statementAnchors(n, statements)}${esc(line) || " "}</td></tr>`;
    }).join("\n");
  }
}
