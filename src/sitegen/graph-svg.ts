import { pathData, polylineCommands } from "../graph-layout/geometry.js";
import { flattenCommands, parsePathData, validateGeometry } from "../graph-layout/validate.js";
import { GraphDiagnosticError, type GraphGeometry, type Rect, type Point } from "../graph-layout/types.js";
import { attr, esc } from "./graph-escape.js";
import type { DisplayNode, MeasuredDisplayGraph, NodeDrawing } from "./graph-project.js";

export interface GraphInteractionPayload {
  nodes: Record<string, {
    label: string; tooltipHtml?: string; tooltipRows?: DisplayNode["tooltipRows"]; incident: string[];
    kind: DisplayNode["kind"] | "dock"; semanticId: string; nodeId: string; href?: string;
  }>;
  edges: Record<string, {
    source: string; target: string; sourceSemanticId: string; targetSemanticId: string;
    kind: string; semanticIds: readonly string[];
  }>;
}
function rect(box: Rect, className = ""): string {
  return `<rect${className ? ` class="${attr(className)}"` : ""} x="${box.x}" y="${box.y}" width="${box.width}" height="${box.height}" rx="4"/>`;
}
function anchor(href: string | undefined, className: string, id: string, label: string, contents: string, statementOwner?: string): string {
  const attributes = `class="${attr(className)}" data-node-id="${attr(id)}" aria-label="${attr(label)}"` +
    (statementOwner ? ` data-statement-detail="${attr(statementOwner)}"` : "");
  // aria-label preserves the accessible name without a native hover rectangle.
  return href ? `<a ${attributes} href="${attr(href)}" role="link">${contents}</a>`
    : `<g ${attributes} tabindex="0">${contents}</g>`;
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
      `<circle class="graph-dock-capsule" cx="${dock.bounds.x + dock.bounds.width / 2}" cy="${dock.bounds.y + dock.bounds.height / 2}" r="${dock.bounds.width / 2}"/>` + labelSvg(dock.lines, "graph-dock-number"), node.id);
  }).join("");
  return box + docks;
}

export function graphInteractionPayload(measured: MeasuredDisplayGraph): GraphInteractionPayload {
  const graph = measured.graph;
  const ports = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const nodes: GraphInteractionPayload["nodes"] = Object.create(null) as GraphInteractionPayload["nodes"];
  for (const node of measured.display.nodes) {
    nodes[node.id] = { label: node.tooltipText ?? node.label, ...(node.tooltipHtml ? { tooltipHtml: node.tooltipHtml } : {}),
      ...(node.tooltipRows ? { tooltipRows: node.tooltipRows } : {}), incident: [], kind: node.kind,
      semanticId: node.semanticId, nodeId: node.id, ...(node.href ? { href: node.href } : {}) };
    // Shorten only local display text; semantic IDs and links stay qualified.
    for (const dock of node.docks) nodes[dock.id] = {
      label: node.ext ? dock.statementId : dock.statementId.replace(/^Lax\d+\./u, ""), incident: [], kind: "dock",
      semanticId: dock.statementId, nodeId: node.id, ...(dock.href ? { href: dock.href } : {}) };
  }
  const edges: GraphInteractionPayload["edges"] = Object.create(null) as GraphInteractionPayload["edges"];
  for (const edge of graph.edges) for (const portId of [edge.sourcePortId, edge.targetPortId]) {
    const port = ports.get(portId)!;
    nodes[port.nodeId]!.incident.push(edge.id);
    const dock = nodes[`dock:${port.semanticEndpointId}`];
    if (dock) dock.incident.push(edge.id);
  }
  for (const edge of graph.edges) {
    const source = ports.get(edge.sourcePortId)!, target = ports.get(edge.targetPortId)!;
    edges[edge.id] = { source: source.nodeId, target: target.nodeId,
      sourceSemanticId: source.semanticEndpointId, targetSemanticId: target.semanticEndpointId,
      kind: edge.kind, semanticIds: edge.semanticIds ?? [] };
  }
  for (const node of Object.values(nodes)) node.incident = [...new Set(node.incident)].sort();
  return { nodes, edges };
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
  const ports = new Map(measured.graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port])));
  const nodeMap = new Map(measured.display.nodes.map((node) => [node.id, node]));
  const placed = new Map(geometry.nodes.map((node) => [node.id, node]));
  const scale = measured.display.nodeScale ?? 1;
  const localProofs = new Map<string, string>();
  const conclusions = new Map(measured.graph.edges.filter((edge) => edge.kind === "conclusion")
    .map((edge) => [ports.get(edge.sourcePortId)!.nodeId, ports.get(edge.targetPortId)!.nodeId]));
  // A sibling assumption is internal to its concept. Keep that entire proof
  // step local, including any external premises, rather than show a false
  // concept-level cycle or an apparently assumption-free proof.
  for (const edge of measured.graph.edges) {
    const source = ports.get(edge.sourcePortId)!, target = ports.get(edge.targetPortId)!;
    if (edge.kind === "assumption" && conclusions.get(target.nodeId) === source.nodeId &&
        nodeMap.get(source.nodeId)!.docks.some((dock) => dock.statementId === source.semanticEndpointId))
      localProofs.set(target.nodeId, source.nodeId);
  }
  const owners = new Map<string, string>(), overviewTargets = new Map<string, Point>();
  for (const edge of measured.graph.edges) {
    const source = ports.get(edge.sourcePortId)!, target = ports.get(edge.targetPortId)!;
    const local = localProofs.get(source.nodeId) ?? localProofs.get(target.nodeId);
    if (local) owners.set(edge.id, local);
    else if (nodeMap.get(target.nodeId)!.docks.some((dock) => dock.statementId === target.semanticEndpointId)) {
      owners.set(edge.id, target.nodeId);
      const body = measured.drawings.get(target.nodeId)!.body;
      const port = geometry.ports.find((port) => port.id === target.id)!;
      overviewTargets.set(target.id, { x: port.x, y: placed.get(target.nodeId)!.y + (body.y + body.height) * scale });
    }
  }
  // Extend only the final dock attachment to the concept's lower border.
  // All other coordinates stay fixed; validate the alternate paths with the
  // hidden dock ink removed before publishing either representation.
  const overview = { ...serialized,
    ports: serialized.ports.map((port) => ({ ...port, ...overviewTargets.get(port.id) })),
    edges: serialized.edges.map((edge) => ({ ...edge, sections: edge.sections.map((section) => {
      const end = section.terminalTargetPortId && overviewTargets.get(section.terminalTargetPortId);
      return end ? { ...section, points: [...section.points, end],
        commands: parsePathData(pathData([...section.commands!, { kind: "L", p: end }])) } : section;
    }) })),
  };
  if (overviewTargets.size) {
    const graph = { ...measured.graph, nodes: measured.graph.nodes.map((node) => ({ ...node,
      labelBoxes: node.labelBoxes.slice(0, measured.drawings.get(node.id)!.lines.length),
      footprints: node.footprints?.filter((footprint) => footprint.kind !== "dock"),
      ports: node.ports.map((port) => {
        const end = overviewTargets.get(port.id), at = placed.get(node.id)!;
        return end ? { ...port, mode: "fixed-position" as const, offset: { x: end.x - at.x, y: end.y - at.y } } : port;
      }),
    })) };
    const checkedOverview = validateGeometry(graph, overview);
    if (!checkedOverview.valid) throw new GraphDiagnosticError(checkedOverview.diagnostics);
  }
  const visibility = (edgeId: string, coarse = false) => owners.has(edgeId)
    ? ` data-statement-${coarse ? "overview" : "detail"}="${attr(owners.get(edgeId)!)}"` : "";
  // Sibling proofs inside one concept are acyclic at statement level and
  // are drawn as ordinary nodes and edges without a cycle envelope.
  const groups = (geometry.groups ?? []).filter((group) => group.kind !== "sibling-proofs")
    .map((group) => `<g class="graph-scc" data-group-id="${attr(group.id)}" aria-label="Display cycle">${rect(group, "cycle-component")}</g>`).join("");
  const renderEdges = (drawing: GraphGeometry, coarse = false) => drawing.edges.filter((edge) => !coarse ||
    edge.sections.some((section) => section.terminalTargetPortId && overviewTargets.has(section.terminalTargetPortId))).map((edge) => {
    const spec = measured.graph.edges.find((e) => e.id === edge.id)!;
    const className = measured.display.kind === "proofs" ? `net-edge ${spec.kind}` : `dag-edge${spec.kind === "proofs" ? " proof-dep" : ""}`;
    return edge.sections.map((section) => `<path class="${attr(className)}" data-edge-id="${attr(edge.id)}"${visibility(edge.id, coarse)} d="${pathData(section.commands!)}"${section.terminalTargetPortId ? ` marker-end="url(#${marker})"` : ""}/>`).join("");
  }).join("");
  const renderHits = (drawing: GraphGeometry, coarse = false) => measured.display.kind === "proofs" ? drawing.edges.filter((edge) => !coarse ||
    edge.sections.some((section) => section.terminalTargetPortId && overviewTargets.has(section.terminalTargetPortId))).map((edge) => edge.sections
    .map((section) => `<path class="graph-edge-hit" data-edge-hit="${attr(edge.id)}"${visibility(edge.id, coarse)} d="${pathData(section.commands!)}"/>`).join(""))
    .join("") : "";
  const edges = renderEdges(serialized) + renderEdges(overview, true);
  const edgeHits = renderHits(serialized) + renderHits(overview, true);
  const nodeScale = measured.display.nodeScale ? ` scale(${measured.display.nodeScale})` : "";
  const nodes = geometry.nodes.map((node) => {
    const display = nodeMap.get(node.id)!, owner = display.docks.length ? node.id : localProofs.get(node.id);
    const local = localProofs.has(node.id) ? ` data-statement-detail="${attr(owner!)}"` : "";
    const region = display.docks.length ? `<rect class="graph-statement-region" width="${node.width / scale}" height="${node.height / scale}"/>` : "";
    const contents = nodeSvg(display, measured.drawings.get(node.id)!);
    return `<g${owner ? ` data-statement-owner="${attr(owner)}"` : ""}${local} transform="translate(${node.x},${node.y})${nodeScale}">${region}${contents}</g>`;
  }).join("");
  // Paint routes over box fills so the label-free attachment areas retain
  // visible statement adapters. The validator still excludes all label ink.
  const { x: drawingX, y, width: drawingWidth, height } = geometry.bounds;
  // Keep a sparse proof network visually balanced without changing any node
  // or route coordinate. The extra view-box space is presentation padding.
  const width = measured.display.kind === "proofs" ? Math.max(720, drawingWidth) : drawingWidth;
  const x = drawingX - (width - drawingWidth) / 2;
  const label = { concepts: "Concept dependency graph", submissions: "Submission dependency graph", proofs: "Proof dependency graph" }[measured.display.kind];
  return `<svg xmlns="http://www.w3.org/2000/svg" class="prepared-graph" width="${width}" height="${height}" viewBox="${x} ${y} ${width} ${height}" aria-label="${label}" data-layout-digest="${attr(geometry.inputDigest)}"><defs><marker id="${marker}" viewBox="0 -5 10 10" refX="9" refY="0" markerWidth="7" markerHeight="7" markerUnits="userSpaceOnUse" orient="auto" overflow="visible"><path d="M1,-4.25 L9,0 L1,4.25 Q3,0 1,-4.25 Z"/></marker></defs><g data-graph-camera>${groups}${edgeHits}${nodes}${edges}</g></svg>`;
}
