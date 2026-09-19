/** A display SCC drawn as a chain. Only one edge per simple cycle has to run
 * against the upward flow, so the members are ranked after cutting a small
 * feedback set (assumption edges first, so every conclusion still rises into
 * the statement it proves), placed in rows from that ranking, and joined by
 * ordinary upward runs. The cut edges alone loop around the column, down a
 * reserved lane on the left; upward runs that span several rows, and the
 * gates of external incidences, use reserved lanes on the right. Anything
 * with east/west attachments, or an internal edge that does not leave a
 * north side for a south side, returns undefined and keeps the generic
 * row-and-lanes interior. The group is still a displayed cycle and keeps its
 * envelope. */
import { simplifyCollinear } from "./geometry.js";
import { compareText } from "./normalize.js";
import { belowBodyEscape, placePorts, portOffsets } from "./ports.js";
import type { Gate, Interior } from "./sibling-groups.js";
import type { LayoutEdge, LayoutProfile, MeasuredGraph, PlacedNode, Point, PortSpec } from "./types.js";

type Incidence = { edge: LayoutEdge; source: PortSpec; target: PortSpec };

const unique = (preferred: string, occupied: Set<string>) => { let id = preferred; while (occupied.has(id)) id = ":" + id; occupied.add(id); return id; };

/** Edges whose removal leaves the members acyclic. Cycles are cut one at a
 * time; within a cycle an assumption edge (leaving a non-proof) is preferred,
 * then the smaller edge id, so the choice is deterministic. */
function feedbackEdges(nodeIds: readonly string[], internal: readonly Incidence[], isProof: (nodeId: string) => boolean): Set<string> {
  const cut = new Set<string>();
  const findCycle = (): Incidence[] | undefined => {
    const state = new Map<string, "open" | "done">(), stack: Incidence[] = [];
    const visit = (nodeId: string): Incidence[] | undefined => {
      state.set(nodeId, "open");
      for (const incidence of internal) {
        if (cut.has(incidence.edge.id) || incidence.source.nodeId !== nodeId) continue;
        const next = incidence.target.nodeId, seen = state.get(next);
        if (seen === "done") continue;
        if (seen === "open") { const from = stack.findIndex((i) => i.source.nodeId === next); return [...stack.slice(from < 0 ? stack.length : from), incidence]; }
        stack.push(incidence);
        const cycle = visit(next);
        if (cycle) return cycle;
        stack.pop();
      }
      state.set(nodeId, "done");
      return undefined;
    };
    for (const nodeId of nodeIds) if (!state.has(nodeId)) { const cycle = visit(nodeId); if (cycle) return cycle; }
    return undefined;
  };
  for (let cycle = findCycle(); cycle; cycle = findCycle()) {
    const choice = [...cycle].sort((a, b) => Number(isProof(a.source.nodeId)) - Number(isProof(b.source.nodeId)) || compareText(a.edge.id, b.edge.id))[0]!;
    cut.add(choice.edge.id);
  }
  return cut;
}

export function chainInteriorFor(graph: MeasuredGraph, members: readonly number[], id: string, profile: LayoutProfile,
  scale: number, occupiedPorts: Set<string>): Interior | undefined {
  const memberNodes = [...members.map((i) => graph.nodes[i]!)].sort((a, b) => compareText(a.id, b.id));
  const ids = new Set(memberNodes.map((n) => n.id)), nodeById = new Map(memberNodes.map((n) => [n.id, n]));
  if (memberNodes.some((n) => n.ports.some((p) => p.side === "east" || p.side === "west"))) return undefined;
  const specById = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const internal: Incidence[] = [], externals: { edge: LayoutEdge; inside: PortSpec; side: "north" | "south" }[] = [];
  for (const edge of [...graph.edges].sort((a, b) => compareText(a.id, b.id))) {
    const source = specById.get(edge.sourcePortId)!, target = specById.get(edge.targetPortId)!;
    const sourceInside = ids.has(source.nodeId), targetInside = ids.has(target.nodeId);
    if (!sourceInside && !targetInside) continue;
    if (sourceInside && targetInside) {
      if (source.side !== "north" || target.side !== "south") return undefined;
      internal.push({ edge, source, target });
    } else if (sourceInside) {
      if (source.side !== "north") return undefined;
      externals.push({ edge, inside: source, side: "north" });
    } else {
      if (target.side !== "south") return undefined;
      externals.push({ edge, inside: target, side: "south" });
    }
  }
  // Rank by longest upward path over the forward edges; rows run top-down
  // from the highest rank.
  const feedback = feedbackEdges(memberNodes.map((n) => n.id), internal, (nodeId) => nodeById.get(nodeId)!.kind === "proof");
  const forward = internal.filter((i) => !feedback.has(i.edge.id));
  const rank = new Map<string, number>(), pending = new Set(memberNodes.map((n) => n.id));
  while (pending.size) {
    const ready = [...pending].filter((nodeId) => forward.every((i) => i.target.nodeId !== nodeId || rank.has(i.source.nodeId)));
    if (!ready.length) return undefined;
    for (const nodeId of ready) { rank.set(nodeId, Math.max(0, ...forward.filter((i) => i.target.nodeId === nodeId).map((i) => rank.get(i.source.nodeId)! + 1))); pending.delete(nodeId); }
  }
  const depth = Math.max(...rank.values()) + 1, rows = Array.from({ length: depth }, () => [] as string[]);
  for (const node of memberNodes) rows[depth - 1 - rank.get(node.id)!]!.push(node.id);
  const rowOf = new Map(rows.flatMap((row, r) => row.map((nodeId) => [nodeId, r] as const)));
  // Every route is planned before any coordinate exists. A run between
  // adjacent rows is direct; everything else leaves through a reserved
  // column: cut edges on the left, longer upward runs and gates on the right.
  const lane = Math.max(profile.portSeparation, 12) * scale, pad = Math.max(profile.clearance + 12, 24) * scale, gap = profile.nodeGap * scale;
  const leftColumns: string[] = [], rightColumns: string[] = [], columnIndex = new Map<string, { side: "left" | "right"; index: number }>();
  const reserveColumn = (side: "left" | "right", key: string) => { const list = side === "left" ? leftColumns : rightColumns; columnIndex.set(key, { side, index: list.length }); list.push(key); };
  const direct = new Set<string>(), straightGate = new Set<string>();
  for (const incidence of internal) {
    const sourceRow = rowOf.get(incidence.source.nodeId)!, targetRow = rowOf.get(incidence.target.nodeId)!;
    if (!feedback.has(incidence.edge.id) && sourceRow === targetRow + 1) direct.add(incidence.edge.id);
    else reserveColumn(feedback.has(incidence.edge.id) ? "left" : "right", incidence.edge.id);
  }
  for (const external of externals) {
    const row = rowOf.get(external.inside.nodeId)!;
    if (external.side === "north" ? row === 0 : row === depth - 1) straightGate.add(external.edge.id);
    else reserveColumn("right", external.edge.id);
  }
  // Horizontal coordinates: rows centred in the content column between the
  // reserved wells. Port abscissae follow from these alone.
  const measured: MeasuredGraph = { nodes: memberNodes, edges: [] }, offsets = portOffsets(measured, {}, profile.portSeparation);
  const rowWidth = (row: readonly string[]) => row.reduce((sum, nodeId) => sum + nodeById.get(nodeId)!.width, 0) + gap * (row.length - 1);
  const contentWidth = Math.max(...rows.map(rowWidth)), contentX = pad + leftColumns.length * lane + pad;
  const width = contentX + contentWidth + pad + rightColumns.length * lane + pad;
  const nodeX = new Map<string, number>();
  for (const row of rows) { let x = contentX + (contentWidth - rowWidth(row)) / 2; for (const nodeId of row) { nodeX.set(nodeId, x); x += nodeById.get(nodeId)!.width + gap; } }
  const portX = (spec: PortSpec) => nodeX.get(spec.nodeId)! + offsets[spec.id]!.x;
  // Lanes: band b is the horizontal gap above row b; band `depth` lies below
  // the last row. A direct run needs a lane only when it has to jog.
  const bands = Array.from({ length: depth + 1 }, () => [] as string[]), laneIndex = new Map<string, number>();
  const reserveLane = (band: number, key: string) => { laneIndex.set(key, bands[band]!.length); bands[band]!.push(key); };
  for (const incidence of internal) {
    const sourceRow = rowOf.get(incidence.source.nodeId)!, targetRow = rowOf.get(incidence.target.nodeId)!;
    if (direct.has(incidence.edge.id)) { if (portX(incidence.source) !== portX(incidence.target)) reserveLane(sourceRow, incidence.edge.id); }
    else { reserveLane(sourceRow, `${incidence.edge.id}:source`); reserveLane(targetRow + 1, `${incidence.edge.id}:target`); }
  }
  for (const external of externals) if (!straightGate.has(external.edge.id)) reserveLane(external.side === "north" ? rowOf.get(external.inside.nodeId)! : rowOf.get(external.inside.nodeId)! + 1, external.edge.id);
  const bandHeight = (band: number) => bands[band]!.length ? pad * 2 + bands[band]!.length * lane : (band === 0 || band === depth ? pad : profile.rankGap * scale);
  const bandTop: number[] = [], rowTop: number[] = [];
  let y = 0;
  rows.forEach((row, r) => { bandTop.push(y); y += bandHeight(r); rowTop.push(y); y += Math.max(...row.map((nodeId) => nodeById.get(nodeId)!.height)); });
  bandTop.push(y); const height = y + bandHeight(depth);
  const nodes: PlacedNode[] = rows.flatMap((row, r) => row.map((nodeId) => ({ id: nodeId, parentId: id, x: nodeX.get(nodeId)!, y: rowTop[r]!, width: nodeById.get(nodeId)!.width, height: nodeById.get(nodeId)!.height })));
  const ports = placePorts(measured, nodes, offsets), portById = new Map(ports.map((p) => [p.id, p]));
  const laneY = (band: number, key: string) => bandTop[band]! + pad + laneIndex.get(key)! * lane;
  const columnX = (key: string) => { const { side, index } = columnIndex.get(key)!; return side === "left" ? pad + index * lane : contentX + contentWidth + pad + index * lane; };
  // A north stem leaves its port upward; statement circles hanging below a
  // concept body use the shared escape so the run never crosses the label.
  const stem = (spec: PortSpec): Point[] => {
    const port = portById.get(spec.id)!;
    if (spec.side !== "north") return [port];
    return belowBodyEscape(nodeById.get(spec.nodeId)!, nodes.find((n) => n.id === spec.nodeId)!, port, profile.portSeparation) ?? [port];
  };
  const routes: Interior["routes"] = new Map();
  for (const incidence of internal) {
    const sourceRow = rowOf.get(incidence.source.nodeId)!, targetRow = rowOf.get(incidence.target.nodeId)!;
    const out = stem(incidence.source), from = out.at(-1)!, to = portById.get(incidence.target.id)!;
    const points = direct.has(incidence.edge.id)
      ? (laneIndex.has(incidence.edge.id) ? [...out, { x: from.x, y: laneY(sourceRow, incidence.edge.id) }, { x: to.x, y: laneY(sourceRow, incidence.edge.id) }, to] : [...out, to])
      : [...out, { x: from.x, y: laneY(sourceRow, `${incidence.edge.id}:source`) }, { x: columnX(incidence.edge.id), y: laneY(sourceRow, `${incidence.edge.id}:source`) },
        { x: columnX(incidence.edge.id), y: laneY(targetRow + 1, `${incidence.edge.id}:target`) }, { x: to.x, y: laneY(targetRow + 1, `${incidence.edge.id}:target`) }, to];
    routes.set(incidence.edge.id, { role: "feedback", points: simplifyCollinear(points) });
  }
  const gates: Gate[] = [], outerPorts: PortSpec[] = [], outerPortIds = new Map<string, string>(), sharedOuter = new Map<string, string>();
  for (const external of externals) {
    const row = rowOf.get(external.inside.nodeId)!, port = portById.get(external.inside.id)!, straight = straightGate.has(external.edge.id);
    let points: Point[];
    if (external.side === "north") {
      const out = stem(external.inside), from = out.at(-1)!;
      points = straight ? [...out, { x: from.x, y: 0 }]
        : [...out, { x: from.x, y: laneY(row, external.edge.id) }, { x: columnX(external.edge.id), y: laneY(row, external.edge.id) }, { x: columnX(external.edge.id), y: 0 }];
    } else {
      points = straight ? [{ x: port.x, y: height }, port]
        : [{ x: columnX(external.edge.id), y: height }, { x: columnX(external.edge.id), y: laneY(row + 1, external.edge.id) }, { x: port.x, y: laneY(row + 1, external.edge.id) }, port];
    }
    points = simplifyCollinear(points);
    const point = external.side === "north" ? points.at(-1)! : points[0]!;
    const gateId = unique(`layout:gate:${JSON.stringify([id, external.edge.id, external.side])}`, occupiedPorts);
    gates.push({ id: gateId, edgeId: external.edge.id, side: external.side, point });
    // Dependents leaving one shared port straight through the boundary meet
    // the condensation at one point; they share a single outer port there so
    // their common trunk is a declared junction, not a coincident run.
    const key = `${external.inside.id}\0${external.side}\0${point.x}\0${point.y}`, outerId = sharedOuter.get(key) ?? gateId;
    if (!sharedOuter.has(key)) {
      sharedOuter.set(key, outerId);
      outerPorts.push({ id: outerId, nodeId: id, semanticEndpointId: external.inside.semanticEndpointId, side: external.side, mode: "fixed-position", offset: point });
    }
    outerPortIds.set(external.edge.id, outerId);
    routes.set(external.edge.id, { role: "group-adapter", points });
  }
  return { id, kind: "cycle", width, height, members, nodes, ports, gates, routes, outerPortIds,
    supernode: { id, kind: "scc", width, height, labelBoxes: [], ports: outerPorts } };
}
