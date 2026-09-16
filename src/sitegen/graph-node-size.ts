import { compareText, normalizeGraph } from "../graph-layout/normalize.js";
import { DEFAULT_PROFILE, GraphDiagnosticError, type MeasuredNode, type PortSpec, type Rect } from "../graph-layout/types.js";
import type { DisplayGraph, GraphLabel, MeasuredDisplayGraph, NodeDrawing } from "./graph-project.js";

function diagnostic(code: string, message: string, ...ids: string[]): never {
  throw new GraphDiagnosticError([{ code, message, ids }]);
}

/** Labels and numbered docks use the same 12px regular SVG text style. Keep
 * the complete request set identical in archive, local and benchmark hosts. */
export function displayLabelRequests(displays: readonly DisplayGraph[]): readonly { text: string; maxWidth: number }[] {
  const texts = new Set<string>();
  for (const display of displays) for (const node of display.nodes) {
    if (node.kind !== "proof") texts.add(node.label);
    for (const dock of node.docks) texts.add(String(dock.ordinal));
  }
  return [...texts].sort(compareText).map((text) => ({ text, maxWidth: 240 }));
}

export function measureDisplayGraph(display: DisplayGraph, labels: ReadonlyMap<string, GraphLabel>, portSeparation = DEFAULT_PROFILE.portSeparation): MeasuredDisplayGraph {
  const measured: MeasuredNode[] = [], drawings = new Map<string, NodeDrawing>();
  const ceil = (n: number) => {
    const scaled = n * 1000, nearest = Math.round(scaled);
    const integral = Math.abs(scaled - nearest) <= 2 * Number.EPSILON * Math.max(1, Math.abs(scaled));
    return (integral ? nearest : Math.ceil(scaled)) / 1000;
  };
  for (const node of display.nodes) {
    const label = labels.get(node.label);
    if (!label && node.kind !== "proof") diagnostic("missing-label-metrics", "Layout requires exact host label metrics", node.id);
    const capacity = (ports: readonly PortSpec[]) => Math.max(0, ...["north", "south"].map((side) => ports.filter((p) => p.side === side).length));
    const bodyPorts = node.ports.filter((p) => !node.docks.some((dock) => dock.statementId === p.semanticEndpointId));
    const cap = capacity(bodyPorts);
    const bodyWidth = ceil(Math.max(node.kind === "proof" ? 28 : label!.width + 20, (cap + 1) * portSeparation));
    const dockLabels = node.docks.map((dock) => {
      const number = labels.get(String(dock.ordinal));
      if (!number) diagnostic("missing-dock-metrics", "Layout requires exact numbered dock metrics", dock.id);
      if (number.lines.length !== 1 || number.lines[0]!.text !== String(dock.ordinal))
        diagnostic("dock-label-metrics", "A fixed dock ordinal must remain one complete measured number", dock.id);
      return number;
    });
    const bodyHeight = node.kind === "proof" ? 28 : ceil(Math.max(28, label!.height + (node.docks.length ? 22 : 14)));
    const outgoingDocks = node.ports.filter((p) => p.side === "north" && node.docks.some((d) => d.statementId === p.semanticEndpointId));
    // Statement circles overlap the box border. Statement-level uses have
    // separate lanes in a label-free attachment area at the bottom of the box.
    const escapeWidth = outgoingDocks.length ? 12 + outgoingDocks.length * portSeparation : 0;
    const dockGap = outgoingDocks.length ? 24 + outgoingDocks.length * portSeparation : -8;
    const attachmentHeight = outgoingDocks.length ? dockGap + 8 : 0;
    const diameters = node.docks.map((dock, i) => ceil(Math.max(20,
      Math.hypot(dockLabels[i]!.width, ...dockLabels[i]!.lines.map((line) => line.ink.height)) + 8,
      (capacity(node.ports.filter((p) => p.semanticEndpointId === dock.statementId)) + 1) * portSeparation)));
    const rowWidth = diameters.reduce((sum, d) => sum + d, 0) + Math.max(0, diameters.length - 1) * portSeparation;
    const contentWidth = Math.max(bodyWidth, rowWidth);
    // Ports and their enclosing envelope use the same upward quantization.
    // This keeps a boundary port inside even when addition leaves the envelope
    // infinitesimally below its exact 0.001px value.
    const width = ceil(contentWidth + escapeWidth);
    const proofRail = node.kind === "proof" && bodyWidth > 36;
    const height = ceil(node.docks.length ? bodyHeight + dockGap + Math.max(...diameters)
      : node.kind === "proof" ? (proofRail ? 40 : 28) : bodyHeight);
    const translateLines = (metric: GraphLabel, x: number, y: number) => metric.lines.map((line) => ({ ...line,
      x: line.x + x, y: line.y + y, ink: { ...line.ink, x: line.ink.x + x, y: line.ink.y + y } }));
    let dockX = escapeWidth + (contentWidth - rowWidth) / 2;
    const dockBoxes = node.docks.map((dock, i) => {
      const diameter = diameters[i]!, number = dockLabels[i]!;
      const bounds = { x: dockX, y: bodyHeight + dockGap, width: diameter, height: diameter };
      dockX += diameter + portSeparation;
      return { ...dock, bounds, lines: translateLines(number, bounds.x + (diameter - number.width) / 2, bounds.y + (diameter - number.height) / 2) };
    });
    const lines = node.kind === "proof" ? [] : label!.lines.map((line) => {
      // Center each line's measured ink, including shorter wrapped lines.
      const dx = escapeWidth + (contentWidth - line.ink.width) / 2 - line.ink.x;
      const dy = (bodyHeight - label!.height) / 2;
      return { ...line, x: line.x + dx, y: line.y + dy,
        ink: { ...line.ink, x: line.ink.x + dx, y: line.ink.y + dy } };
    });
    const body: Rect = node.kind === "proof" ? { x: (bodyWidth - 28) / 2, y: 0, width: 28, height: 28 }
      : { x: escapeWidth, y: 0, width: contentWidth, height: bodyHeight };
    const ports = node.ports.map((port): PortSpec => {
      const dock = dockBoxes.find((d) => d.statementId === port.semanticEndpointId);
      if (!node.docks.length) return { ...port };
      const region = dock?.bounds ?? body;
      const peers = node.ports.filter((p) => p.side === port.side && (dock ? p.semanticEndpointId === dock.statementId : !node.docks.some((d) => d.statementId === p.semanticEndpointId))).sort((a, b) => compareText(a.id, b.id));
      const slot = peers.findIndex((p) => p.id === port.id);
      const dx = (slot - (peers.length - 1) / 2) * portSeparation;
      const radius = region.width / 2;
      return { ...port, mode: "fixed-position", offset: {
        x: ceil(region.x + radius + dx),
        y: ceil(dock ? region.y + radius + (port.side === "north" ? -1 : 1) * Math.sqrt(radius * radius - dx * dx)
          : port.side === "north" ? region.y : region.y + region.height),
      } };
    });
    const footprints: NonNullable<MeasuredNode["footprints"]>[number][] = [
      { id: `${node.id}:body`, kind: "body", bounds: body },
      ...dockBoxes.map((dock) => ({ id: dock.id, kind: "dock" as const, bounds: dock.bounds, semanticEndpointId: dock.statementId })),
    ];
    if (proofRail) footprints.push({ id: `${node.id}:assumption-rail`, kind: "rail", bounds: { x: 0, y: 28, width, height: height - 28 } });
    if (attachmentHeight) footprints.push({ id: `${node.id}:attachment-area`, kind: "attachment-area",
      bounds: { x: body.x, y: bodyHeight, width: body.width, height: attachmentHeight } });
    measured.push({ id: node.id, kind: node.kind, width, height,
      labelBoxes: [...lines, ...dockBoxes.flatMap((dock) => dock.lines)].map((line) => line.ink), ports, footprints });
    drawings.set(node.id, { body: { ...body, height: body.height + attachmentHeight }, lines, docks: dockBoxes, proofRail });
  }
  // Enlarge the measured obstacles and attachment points before layout. The
  // serializer applies the same scale to the original node drawing, keeping
  // font ink, numbered docks, proof rails and edge endpoints in agreement.
  const scale = display.nodeScale ?? 1;
  const scaleRect = (box: Rect): Rect => ({ x: box.x * scale, y: box.y * scale,
    width: box.width * scale, height: box.height * scale });
  const nodes = scale === 1 ? measured : measured.map((node) => ({ ...node,
    width: node.width * scale, height: node.height * scale,
    labelBoxes: node.labelBoxes.map(scaleRect),
    ports: node.ports.map((port) => port.offset ? { ...port,
      offset: { x: port.offset.x * scale, y: port.offset.y * scale } } : port),
    footprints: node.footprints?.map((footprint) => ({ ...footprint, bounds: scaleRect(footprint.bounds) })),
  }));
  return { display, graph: normalizeGraph({ nodes, edges: display.edges }), drawings };
}
