/** A concept whose numbered statements prove one another is a display SCC
 * only because all of its statements share one concept box; at statement
 * level the incidences are acyclic. Such a group is drawn locally instead of
 * with the generic row-and-lanes envelope: every proof sits directly below
 * the dock it proves, its sibling assumptions drop from their own docks into
 * rails below the proof, and the conclusion rises straight back into its
 * dock. No cycle envelope is displayed. Anything outside this exact pattern
 * returns undefined and keeps the conservative interior. */
import { simplifyCollinear } from "./geometry.js";
import { compareText } from "./normalize.js";
import { placePorts, portOffsets, type PortOffsets } from "./ports.js";
import type { LayoutEdge, LayoutProfile, MeasuredGraph, MeasuredNode, PlacedGroup, PlacedNode, PlacedPort, Point, PortSpec } from "./types.js";

export type Gate = NonNullable<PlacedGroup["gates"]>[number];
export type Interior = {
  id: string; kind: NonNullable<PlacedGroup["kind"]>; width: number; height: number; members: readonly number[];
  nodes: PlacedNode[]; ports: PlacedPort[]; gates: Gate[];
  routes: Map<string, { role: "feedback" | "group-adapter"; points: Point[] }>;
  /** Outer condensation port per external edge when it differs from the
   * edge's own gate: edges leaving one shared source port share one. */
  outerPortIds?: Map<string, string>;
  supernode: MeasuredNode;
};
type Incidence = { edge: LayoutEdge; source: PortSpec; target: PortSpec };
type Interval = { lo: number; hi: number };

const unique = (preferred: string, occupied: Set<string>) => { let id = preferred; while (occupied.has(id)) id = ":" + id; occupied.add(id); return id; };

/** Nearest value to `wanted` outside every forbidden open interval, preferring
 * values inside `within` when that is possible. Forbidden intervals are
 * treated as closed so a box never touches a column it must clear. */
function nearestFree(wanted: number, forbidden: readonly Interval[], within?: Interval): number {
  const free = (x: number) => forbidden.every((f) => x <= f.lo || x >= f.hi);
  const candidates = [wanted, ...forbidden.flatMap((f) => [f.lo, f.hi])];
  if (within) candidates.push(Math.min(Math.max(wanted, within.lo), within.hi), within.lo, within.hi);
  const inside = (x: number) => !within || (x >= within.lo && x <= within.hi);
  const rank = (x: number) => Math.abs(x - wanted);
  const allowed = candidates.filter(free);
  const preferred = allowed.filter(inside).sort((a, b) => rank(a) - rank(b));
  const fallback = allowed.sort((a, b) => rank(a) - rank(b));
  const chosen = preferred[0] ?? fallback[0];
  if (chosen === undefined) throw new Error("no free position");
  return chosen;
}

export function siblingInteriorFor(graph: MeasuredGraph, members: readonly number[], id: string, profile: LayoutProfile,
  scale: number, occupiedPorts: Set<string>): Interior | undefined {
  const memberNodes = members.map((i) => graph.nodes[i]!);
  const hosts = memberNodes.filter((n) => n.kind !== "proof"), proofs = memberNodes.filter((n) => n.kind === "proof").sort((a, b) => compareText(a.id, b.id));
  if (hosts.length !== 1 || !proofs.length) return undefined;
  const concept = hosts[0]!, ids = new Set(memberNodes.map((n) => n.id));
  const body = concept.footprints?.find((f) => f.kind === "body")?.bounds;
  const docks = (concept.footprints ?? []).filter((f) => f.kind === "dock" && f.semanticEndpointId);
  if (!body || !docks.length) return undefined;
  if (concept.ports.some((p) => p.mode !== "fixed-position" || !p.offset)) return undefined;
  if (concept.ports.some((p) => p.side === "north" && p.offset!.y > body.y + body.height)) return undefined;
  const specById = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const dockOf = (spec: PortSpec) => spec.nodeId === concept.id ? docks.find((d) => d.semanticEndpointId === spec.semanticEndpointId) : undefined;
  const stems: Incidence[] = [], conclusions = new Map<string, Incidence>();
  const externals: { edge: LayoutEdge; inside: PortSpec; side: "north" | "south" }[] = [];
  for (const edge of graph.edges) {
    const source = specById.get(edge.sourcePortId)!, target = specById.get(edge.targetPortId)!;
    const sourceInside = ids.has(source.nodeId), targetInside = ids.has(target.nodeId);
    if (!sourceInside && !targetInside) continue;
    if (sourceInside && targetInside) {
      if (source.nodeId === concept.id && source.side === "south" && dockOf(source) && target.nodeId !== concept.id && target.side === "south")
        stems.push({ edge, source, target });
      else if (source.nodeId !== concept.id && source.side === "north" && target.nodeId === concept.id && target.side === "south" && dockOf(target)) {
        if (conclusions.has(source.nodeId)) return undefined;
        conclusions.set(source.nodeId, { edge, source, target });
      } else return undefined;
    } else if (sourceInside) {
      if (source.nodeId !== concept.id || source.side !== "north" || dockOf(source)) return undefined;
      externals.push({ edge, inside: source, side: "north" });
    } else {
      if (target.side !== "south" || (target.nodeId === concept.id && !dockOf(target))) return undefined;
      externals.push({ edge, inside: target, side: "south" });
    }
  }
  for (const proof of proofs) {
    const conclusion = conclusions.get(proof.id);
    if (!conclusion || !proof.ports.every((p) => p.side === "south" || p.id === conclusion.source.id)) return undefined;
  }
  // Concept-local coordinates first; the envelope is translated at the end.
  const pad = 24 * scale, lane = profile.portSeparation * scale, margin = 8 * scale, gap = 24 * scale;
  const conceptOffsets = portOffsets({ nodes: [concept], edges: [] }, {}, profile.portSeparation);
  const at = (spec: PortSpec): Point => conceptOffsets[spec.id]!;
  const blocked: Interval[] = [];
  const column = (x: number) => blocked.push({ lo: x - margin, hi: x + margin });
  for (const external of externals) if (external.side === "south" && external.inside.nodeId === concept.id) column(at(external.inside).x);
  for (const stem of stems) column(at(stem.source).x);
  const placedProofs = new Map<string, { x: number; y: number; width: number; height: number; portX: number }>();
  const offsets: Record<string, Point> = { ...conceptOffsets };
  const rowY = concept.height + gap;
  const byDock = [...proofs].sort((a, b) => at(conclusions.get(a.id)!.target).x - at(conclusions.get(b.id)!.target).x || compareText(a.id, b.id));
  for (const proof of byDock) {
    const conclusion = conclusions.get(proof.id)!, cx = at(conclusion.target).x, w = proof.width, h = proof.height;
    const forbidden = blocked.map((b) => ({ lo: b.lo - w, hi: b.hi }));
    let x: number;
    try { x = nearestFree(cx - w / 2, forbidden, { lo: cx - (w - 4), hi: cx - 4 }); } catch { return undefined; }
    const portX = conclusion.source.mode === "fixed-position" ? conclusion.source.offset!.x
      : Math.min(Math.max(cx - x, 4), w - 4);
    placedProofs.set(proof.id, { x, y: rowY, width: w, height: h, portX });
    offsets[conclusion.source.id] = { x: portX, y: 0 };
    blocked.push({ lo: x - margin, hi: x + w + margin });
  }
  const maxBottom = Math.max(...[...placedProofs.values()].map((p) => p.y + p.height));
  const routes: Interior["routes"] = new Map();
  let depth = 0;
  const railY = () => maxBottom + 12 * scale + depth++ * lane;
  for (const proof of byDock) {
    const box = placedProofs.get(proof.id)!, center = box.x + box.width / 2;
    const south = proof.ports.filter((p) => p.side === "south"), n = south.length;
    if (n && (n - 1) * lane > box.width - 8) return undefined;
    const slot = (i: number) => box.x + box.width / 2 + (i - (n - 1) / 2) * lane;
    const own = stems.filter((s) => s.target.nodeId === proof.id);
    const left = own.filter((s) => at(s.source).x < center).sort((a, b) => at(b.source).x - at(a.source).x);
    const right = own.filter((s) => at(s.source).x >= center).sort((a, b) => at(a.source).x - at(b.source).x);
    const middle = south.filter((p) => !own.some((s) => s.target.id === p.id)).sort((a, b) => compareText(a.id, b.id));
    const order = [...left.map((s) => s.target), ...middle, ...right.map((s) => s.target).reverse()];
    order.forEach((port, i) => { offsets[port.id] = { x: slot(i) - box.x, y: box.height }; });
    for (const stem of [...left, ...right]) {
      const source = at(stem.source), targetX = box.x + offsets[stem.target.id]!.x, y = railY();
      routes.set(stem.edge.id, { role: "feedback", points: simplifyCollinear([source, { x: source.x, y }, { x: targetX, y }, { x: targetX, y: box.y + box.height }]) });
    }
    const conclusion = conclusions.get(proof.id)!, from = { x: box.x + box.portX, y: box.y }, to = at(conclusion.target);
    const midY = to.y + (box.y - to.y) / 2;
    routes.set(conclusion.edge.id, { role: "feedback", points: simplifyCollinear(from.x === to.x ? [from, to] : [from, { x: from.x, y: midY }, { x: to.x, y: midY }, to]) });
  }
  const proofBoxes = [...placedProofs.values()];
  const minX = Math.min(0, ...proofBoxes.map((p) => p.x)) - pad, maxX = Math.max(concept.width, ...proofBoxes.map((p) => p.x + p.width)) + pad;
  const bottom = (depth ? maxBottom + 12 * scale + (depth - 1) * lane : maxBottom) + pad;
  const shift: Point = { x: -minX, y: pad }, width = maxX - minX, height = bottom + pad;
  const move = (p: Point): Point => ({ x: p.x + shift.x, y: p.y + shift.y });
  const nodes: PlacedNode[] = [{ id: concept.id, parentId: id, ...move({ x: 0, y: 0 }), width: concept.width, height: concept.height },
    ...proofs.map((proof) => { const box = placedProofs.get(proof.id)!; return { id: proof.id, parentId: id, ...move(box), width: box.width, height: box.height }; })];
  const measured: MeasuredGraph = { nodes: [concept, ...proofs], edges: [] };
  const ports = placePorts(measured, nodes, offsets as PortOffsets), portById = new Map(ports.map((p) => [p.id, p]));
  for (const [edgeId, route] of routes) routes.set(edgeId, { ...route, points: route.points.map(move) });
  const gates: Gate[] = [], outerPorts: PortSpec[] = [], outerPortIds = new Map<string, string>(), sharedOuter = new Map<string, string>();
  for (const external of externals) {
    const port = portById.get(external.inside.id)!;
    const gateId = unique(`layout:gate:${JSON.stringify([id, external.edge.id, external.side])}`, occupiedPorts);
    const point = { x: port.x, y: external.side === "north" ? 0 : height };
    gates.push({ id: gateId, edgeId: external.edge.id, side: external.side, point });
    // Several dependents may leave the concept's one shared assumption-source
    // port. Each keeps its own gate, but the condensation sees a single outer
    // port for them, so their common trunk is a declared junction there, not
    // a coincident run between distinct ports at one point.
    const key = `${external.inside.id}\0${external.side}`, outerId = sharedOuter.get(key) ?? gateId;
    if (!sharedOuter.has(key)) {
      sharedOuter.set(key, outerId);
      outerPorts.push({ id: outerId, nodeId: id, semanticEndpointId: external.inside.semanticEndpointId, side: external.side, mode: "fixed-position", offset: point });
    }
    outerPortIds.set(external.edge.id, outerId);
    routes.set(external.edge.id, { role: "group-adapter", points: external.side === "north" ? [{ x: port.x, y: port.y }, point] : [point, { x: port.x, y: port.y }] });
  }
  return { id, kind: "sibling-proofs", width, height, members, nodes, ports, gates, routes, outerPortIds,
    supernode: { id, kind: "scc", width, height, labelBoxes: [], ports: outerPorts } };
}
