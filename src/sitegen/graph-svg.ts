import { pathData, polylineCommands } from "../graph-layout/geometry.js";
import { flattenCommands, parsePathData, validateGeometry } from "../graph-layout/validate.js";
import { GraphDiagnosticError, type GraphGeometry, type Rect } from "../graph-layout/types.js";
import { attr, esc } from "./graph-escape.js";
import type { DisplayNode, MeasuredDisplayGraph, NodeDrawing } from "./graph-project.js";

export interface GraphInteractionPayload {
  nodes: Record<string, { label: string; tooltipHtml?: string; incident: string[] }>;
}
function rect(box: Rect, className = ""): string {
  return `<rect${className ? ` class="${attr(className)}"` : ""} x="${box.x}" y="${box.y}" width="${box.width}" height="${box.height}" rx="4"/>`;
}
function anchor(href: string | undefined, className: string, id: string, label: string, contents: string): string {
  const attributes = `class="${attr(className)}" data-node-id="${attr(id)}" aria-label="${attr(label)}"`;
  return href ? `<a ${attributes} href="${attr(href)}" role="link"><title>${esc(label)}</title>${contents}</a>`
    : `<g ${attributes} tabindex="0"><title>${esc(label)}</title>${contents}</g>`;
}
/** Matches the host's single text element with independently positioned
 * tspans; baselines and ink extents were measured before node placement. */
function labelSvg(lines: NodeDrawing["lines"], className: string): string {
  return `<text class="${className}" xml:space="preserve">${lines.map((line) => `<tspan x="${line.x}" y="${line.y}">${esc(line.text)}</tspan>`).join("")}</text>`;
}
function nodeSvg(node: DisplayNode, drawing: NodeDrawing): string {
  if (node.kind === "proof") {
    const cx = drawing.body.x + drawing.body.width / 2;
    // The turnstile stays compact. A visible rail connects multiple spaced
    // attachments to this particular proof's AND junction.
    const rail = drawing.proofRail ? `<path class="graph-port-rail" d="M0,40 H${drawing.body.width + 2 * drawing.body.x} M${cx},40 V28"/>` : "";
    return anchor(node.href, `net-proof${node.ext ? " ext" : ""}`, node.id, `Proof ${node.semanticId}`,
      `${rail}${rect(drawing.body)}<path class="graph-turnstile" d="M${cx - 5},8 V20 M${cx - 5},14 H${cx + 6}"/>`);
  }
  const cls = `${node.kind === "submission" ? "dag-node submission" : "net-node"} ${node.status}${node.ext ? " ext" : ""}`;
  const text = labelSvg(drawing.lines, "graph-label");
  const box = anchor(node.href, cls, node.id, `${node.label} (${node.semanticId})`, rect(drawing.body) + text);
  const docks = drawing.docks.map((dock) => {
    return anchor(dock.href, `net-dock ${dock.status}${node.ext ? " ext" : ""}`, dock.id,
      `${node.label}, statement ${dock.ordinal} (${dock.statementId})`,
      rect(dock.bounds, "graph-dock-capsule") + labelSvg(dock.lines, "graph-dock-number"));
  }).join("");
  return box + docks;
}

export function graphInteractionPayload(measured: MeasuredDisplayGraph): GraphInteractionPayload {
  const graph = measured.graph;
  const ports = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const nodes: GraphInteractionPayload["nodes"] = Object.create(null) as GraphInteractionPayload["nodes"];
  for (const node of measured.display.nodes) {
    nodes[node.id] = { label: node.label, ...(node.tooltipHtml ? { tooltipHtml: node.tooltipHtml } : {}), incident: [] };
    for (const dock of node.docks) nodes[dock.id] = { label: `${node.label}, statement ${dock.ordinal}`,
      ...(dock.tooltipHtml ? { tooltipHtml: dock.tooltipHtml } : {}), incident: [] };
  }
  for (const edge of graph.edges) for (const portId of [edge.sourcePortId, edge.targetPortId]) {
    const port = ports.get(portId)!;
    nodes[port.nodeId]!.incident.push(edge.id);
    const dock = nodes[`dock:${port.semanticEndpointId}`];
    if (dock) dock.incident.push(edge.id);
  }
  for (const node of Object.values(nodes)) node.incident = [...new Set(node.incident)].sort();
  return { nodes };
}

/** SVG is the final checked representation. Serialization is read back using
 * an independent parser, so numeric rounding cannot invalidate a route after
 * the layout validator accepted its in-memory form. Real anchors work with
 * JavaScript disabled; the browser never constructs the default graph. */
export function graphSvg(measured: MeasuredDisplayGraph, geometry: GraphGeometry, markerPrefix: string): string {
  const serialized = { ...geometry, edges: geometry.edges.map((edge) => ({ ...edge, sections: edge.sections.map((section) => ({ ...section,
    commands: parsePathData(pathData(section.commands ?? polylineCommands(section.points))) })) })) };
  for (const edge of serialized.edges) for (const section of edge.sections) flattenCommands(section.commands!);
  const checked = validateGeometry(measured.graph, serialized);
  if (!checked.valid) throw new GraphDiagnosticError(checked.diagnostics);
  const marker = `graph-arrow-${markerPrefix}`;
  const groups = (geometry.groups ?? []).map((group) => `<g class="graph-scc" data-group-id="${attr(group.id)}" aria-label="Display cycle"><title>Display cycle</title>${rect(group, "cycle-component")}</g>`).join("");
  const edges = serialized.edges.map((edge) => {
    const spec = measured.graph.edges.find((e) => e.id === edge.id)!;
    const className = measured.display.kind === "proofs" ? `net-edge ${spec.kind}` : `dag-edge${spec.kind === "proofs" ? " proof-dep" : ""}`;
    return edge.sections.map((section) => `<path class="${attr(className)}" data-edge-id="${attr(edge.id)}" d="${pathData(section.commands!)}"${section.terminalTargetPortId ? ` marker-end="url(#${marker})"` : ""}/>`).join("");
  }).join("");
  const nodeMap = new Map(measured.display.nodes.map((node) => [node.id, node]));
  const nodes = geometry.nodes.map((node) => `<g transform="translate(${node.x},${node.y})">${nodeSvg(nodeMap.get(node.id)!, measured.drawings.get(node.id)!)}</g>`).join("");
  const { x, y, width, height } = geometry.bounds;
  const label = { concepts: "Concept dependency graph", submissions: "Submission dependency graph", proofs: "Proof dependency graph" }[measured.display.kind];
  return `<svg xmlns="http://www.w3.org/2000/svg" class="prepared-graph" width="${width}" height="${height}" viewBox="${x} ${y} ${width} ${height}" aria-label="${label}" data-layout-digest="${attr(geometry.inputDigest)}"><defs><marker id="${marker}" viewBox="0 -5 10 10" refX="9" refY="0" markerWidth="7" markerHeight="7" markerUnits="userSpaceOnUse" orient="auto" overflow="visible"><path d="M1,-4.25 L9,0 L1,4.25 Q3,0 1,-4.25 Z"/></marker></defs><g data-graph-camera>${groups}${edges}${nodes}</g></svg>`;
}
