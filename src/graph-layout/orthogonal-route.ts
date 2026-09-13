/** Object-avoiding visibility routing after Wybrow–Marriott–Stuckey (2009).
 * We search a LOCAL band/group visibility graph, with direction in every
 * state. The inter-edge and corridor restrictions are documented heuristics;
 * no simultaneous/global optimality claim follows from this shortest path. */
import { compareText } from "./normalize.js";
import { quantizeGeometry, simplifyCollinear } from "./geometry.js";
import { protectedEdgeSections, type CorridorPlacement } from "./corridors.js";
import type { ProperGraph } from "./proper-graph.js";
import { DEFAULT_PROFILE, type Diagnostic, type GraphGeometry, type LayoutProfile, type Point, type Rect } from "./types.js";
import { validateGeometry } from "./validate.js";

const EPS = 1e-7;
export type Direction = "north" | "east" | "south" | "west";
const directions: Direction[] = ["north", "east", "south", "west"];
const key = (p: Point) => `${p.x},${p.y}`;
type Segment = Readonly<{ a: Point; b: Point }>;
type Visibility = { points: Point[]; adjacency: { to: number; direction: number; length: number; extra: number }[][]; start: number; target: number };
export type OrthogonalOptions = Readonly<{
  bounds: Rect; obstacles?: readonly Rect[]; fixedRoutes?: readonly (readonly Point[])[];
  interesting?: readonly Point[]; monotone?: boolean;
  startDirection?: Direction; targetDirection?: Direction;
  requireStartDirection?: boolean; requireTargetDirection?: boolean;
  bendPenalty?: number; crossingPenalty?: number; expansionBudget?: number;
  visibilityBudget?: number; heuristic?: "manhattan" | "zero";
}>;
export type OrthogonalResult = Readonly<{
  points?: readonly Point[]; cost?: number; expansions: number; visibilityVertices: number;
  termination: "shortest-in-visibility-graph" | "budget-exhausted" | "no-route";
}>;

/** Routing-side open-interior predicate, deliberately independent of the
 * validator's Liang–Barsky clipping. Expanded obstacles retain clearance. */
function obstructed(a: Point, b: Point, rect: Rect): boolean {
  if (Math.abs(a.x - b.x) < EPS) return a.x > rect.x + EPS && a.x < rect.x + rect.width - EPS
    && Math.min(a.y, b.y) < rect.y + rect.height - EPS && Math.max(a.y, b.y) > rect.y + EPS;
  return a.y > rect.y + EPS && a.y < rect.y + rect.height - EPS
    && Math.min(a.x, b.x) < rect.x + rect.width - EPS && Math.max(a.x, b.x) > rect.x + EPS;
}
function segmentPenalty(a: Point, b: Point, routes: readonly Segment[], crossingPenalty: number): number {
  let crosses = 0;
  const horizontal = Math.abs(a.y - b.y) < EPS;
  for (const edge of routes) {
    const otherHorizontal = Math.abs(edge.a.y - edge.b.y) < EPS;
    if (horizontal === otherHorizontal) {
      if (horizontal ? Math.abs(a.y - edge.a.y) > EPS : Math.abs(a.x - edge.a.x) > EPS) continue;
      const [lo, hi, otherLo, otherHi] = horizontal ? [Math.min(a.x, b.x), Math.max(a.x, b.x), Math.min(edge.a.x, edge.b.x), Math.max(edge.a.x, edge.b.x)]
        : [Math.min(a.y, b.y), Math.max(a.y, b.y), Math.min(edge.a.y, edge.b.y), Math.max(edge.a.y, edge.b.y)];
      if (Math.min(hi, otherHi) - Math.max(lo, otherLo) > EPS) return Infinity;
    } else {
      const h = horizontal ? { a, b } : edge, v = horizontal ? edge : { a, b };
      if (v.a.x >= Math.min(h.a.x, h.b.x) - EPS && v.a.x <= Math.max(h.a.x, h.b.x) + EPS
        && h.a.y >= Math.min(v.a.y, v.b.y) - EPS && h.a.y <= Math.max(v.a.y, v.b.y) + EPS) crosses++;
    }
  }
  return crosses * crossingPenalty;
}

function buildVisibility(start: Point, target: Point, options: OrthogonalOptions): Visibility | undefined {
  const bounds = options.bounds, right = bounds.x + bounds.width, bottom = bounds.y + bounds.height;
  const obstacles = options.obstacles ?? [], budget = options.visibilityBudget ?? options.expansionBudget ?? 100_000;
  const inBounds = (p: Point) => p.x >= bounds.x - EPS && p.x <= right + EPS && p.y >= bounds.y - EPS && p.y <= bottom + EPS;
  const inObstacle = (p: Point) => obstacles.some((r) => p.x > r.x + EPS && p.x < r.x + r.width - EPS && p.y > r.y + EPS && p.y < r.y + r.height - EPS);
  if (!inBounds(start) || !inBounds(target) || inObstacle(start) || inObstacle(target)) return { points: [], adjacency: [], start: -1, target: -1 };
  const interesting = [start, target, ...(options.interesting ?? []), ...obstacles.flatMap((r) => [
    { x: r.x, y: r.y }, { x: r.x + r.width, y: r.y }, { x: r.x, y: r.y + r.height }, { x: r.x + r.width, y: r.y + r.height },
  ])].filter((p) => inBounds(p) && !inObstacle(p));
  type Line = { at: number; lo: number; hi: number; ids: number[] };
  const horizontal = new Map<string, Line>(), vertical = new Map<string, Line>();
  for (const p of interesting) {
    let left = bounds.x, end = right, top = bounds.y, down = bottom;
    for (const r of obstacles) {
      if (p.y > r.y + EPS && p.y < r.y + r.height - EPS) {
        if (r.x + r.width <= p.x + EPS) left = Math.max(left, r.x + r.width);
        if (r.x >= p.x - EPS) end = Math.min(end, r.x);
      }
      if (p.x > r.x + EPS && p.x < r.x + r.width - EPS) {
        if (r.y + r.height <= p.y + EPS) top = Math.max(top, r.y + r.height);
        if (r.y >= p.y - EPS) down = Math.min(down, r.y);
      }
    }
    horizontal.set(`${p.y}:${left}:${end}`, { at: p.y, lo: left, hi: end, ids: [] });
    vertical.set(`${p.x}:${top}:${down}`, { at: p.x, lo: top, hi: down, ids: [] });
  }
  const points: Point[] = [], index = new Map<string, number>();
  const vertex = (p: Point) => { const k = key(p), existing = index.get(k); if (existing !== undefined) return existing; const id = points.length; index.set(k, id); points.push(p); return id; };
  // Intersect visible rays, not the entire drawing's coordinate Cartesian
  // product. The caller bounds each search to one band or one group.
  let operations = 0;
  for (const h of horizontal.values()) for (const v of vertical.values()) {
    if (++operations > budget * 8 || points.length > budget) return undefined;
    if (v.at < h.lo - EPS || v.at > h.hi + EPS || h.at < v.lo - EPS || h.at > v.hi + EPS) continue;
    const id = vertex({ x: v.at, y: h.at }); h.ids.push(id); v.ids.push(id);
  }
  const adjacency: Visibility["adjacency"] = points.map(() => []), fixed: Segment[] = [];
  for (const route of options.fixedRoutes ?? []) for (let i = 1; i < route.length; i++) fixed.push({ a: route[i - 1]!, b: route[i]! });
  const add = (a: number, b: number, direction: number) => {
    const u = points[a]!, v = points[b]!;
    if (obstacles.some((r) => obstructed(u, v, r))) return;
    const extra = segmentPenalty(u, v, fixed, options.crossingPenalty ?? 40);
    if (!Number.isFinite(extra)) return;
    const length = Math.abs(u.x - v.x) + Math.abs(u.y - v.y);
    adjacency[a]!.push({ to: b, direction, length, extra }); adjacency[b]!.push({ to: a, direction: (direction + 2) % 4, length, extra });
  };
  for (const h of horizontal.values()) { h.ids.sort((a, b) => points[a]!.x - points[b]!.x); for (let i = 1; i < h.ids.length; i++) add(h.ids[i - 1]!, h.ids[i]!, 1); }
  for (const v of vertical.values()) { v.ids.sort((a, b) => points[a]!.y - points[b]!.y); for (let i = 1; i < v.ids.length; i++) add(v.ids[i - 1]!, v.ids[i]!, 2); }
  for (const edges of adjacency) edges.sort((a, b) => a.direction - b.direction || a.to - b.to);
  return { points, adjacency, start: index.get(key(start)) ?? -1, target: index.get(key(target)) ?? -1 };
}

type QueueItem = { state: number; g: number; f: number; serial: number };
class MinHeap {
  private values: QueueItem[] = [];
  get length() { return this.values.length; }
  get minimum() { return this.values[0]; }
  private less(a: QueueItem, b: QueueItem) { return a.f < b.f || (a.f === b.f && (a.g < b.g || (a.g === b.g && a.serial < b.serial))); }
  push(value: QueueItem) { let i = this.values.length; this.values.push(value); while (i) { const parent = (i - 1) >>> 1; if (!this.less(value, this.values[parent]!)) break; this.values[i] = this.values[parent]!; i = parent; } this.values[i] = value; }
  pop(): QueueItem { const result = this.values[0]!, end = this.values.pop()!; if (this.values.length) { let i = 0; while (i * 2 + 1 < this.values.length) { let child = i * 2 + 1; if (child + 1 < this.values.length && this.less(this.values[child + 1]!, this.values[child]!)) child++; if (!this.less(this.values[child]!, end)) break; this.values[i] = this.values[child]!; i = child; } this.values[i] = end; } return result; }
}

export function orthogonalPath(start: Point, target: Point, options: OrthogonalOptions): OrthogonalResult {
  const visibility = buildVisibility(start, target, options), limit = options.expansionBudget ?? 100_000;
  if (!visibility) return { expansions: 0, visibilityVertices: 0, termination: "budget-exhausted" };
  const { points, adjacency } = visibility;
  if (visibility.start < 0 || visibility.target < 0) return { expansions: 0, visibilityVertices: points.length, termination: "no-route" };
  const startDirection = options.startDirection ? directions.indexOf(options.startDirection) : 4, targetDirection = options.targetDirection ? directions.indexOf(options.targetDirection) : 4;
  const initial = visibility.start * 5 + startDirection, distance = new Float64Array(points.length * 5).fill(Infinity), previous = new Int32Array(points.length * 5).fill(-1), heap = new MinHeap();
  const heuristic = (p: Point) => options.heuristic === "zero" ? 0 : Math.abs(p.x - target.x) + Math.abs(p.y - target.y);
  let serial = 0, expansions = 0, bestState = -1, bestCost = Infinity;
  const finish = (): OrthogonalResult => {
    const route: Point[] = []; let state = bestState;
    while (state !== -1) { route.push(points[Math.floor(state / 5)]!); state = previous[state]!; }
    route.reverse();
    return { points: simplifyCollinear(route), cost: bestCost, expansions, visibilityVertices: points.length, termination: "shortest-in-visibility-graph" };
  };
  distance[initial] = 0; heap.push({ state: initial, g: 0, f: heuristic(start), serial: serial++ });
  while (heap.length) {
    if (bestState >= 0 && heap.minimum!.f >= bestCost - EPS) return finish();
    if (expansions >= limit) return { expansions, visibilityVertices: points.length, termination: "budget-exhausted" };
    const current = heap.pop();
    if (current.g > distance[current.state]! + EPS) continue;
    expansions++;
    const vertex = Math.floor(current.state / 5), incoming = current.state % 5;
    if (vertex === visibility.target && (!options.requireTargetDirection || targetDirection === 4 || incoming === targetDirection)) {
      const cost = current.g + (targetDirection !== 4 && incoming !== 4 && incoming !== targetDirection ? options.bendPenalty ?? 12 : 0);
      if (cost < bestCost) { bestCost = cost; bestState = current.state; }
      continue;
    }
    for (const edge of adjacency[vertex]!) {
      if (options.monotone !== false && edge.direction === 2) continue;
      if (incoming !== 4 && edge.direction === (incoming + 2) % 4) continue;
      if (current.state === initial && options.requireStartDirection && startDirection !== 4 && edge.direction !== startDirection) continue;
      const bends = incoming === 4 || incoming === edge.direction ? 0 : 1;
      const cost = current.g + edge.length + edge.extra + bends * (options.bendPenalty ?? 12), state = edge.to * 5 + edge.direction;
      if (cost >= distance[state]! - EPS) continue;
      distance[state] = cost; previous[state] = current.state;
      heap.push({ state, g: cost, f: cost + heuristic(points[edge.to]!), serial: serial++ });
    }
  }
  if (bestState >= 0) return finish();
  return { expansions, visibilityVertices: points.length, termination: "no-route" };
}

export type OrthogonalCandidateResult = Readonly<{
  candidates: readonly GraphGeometry[]; diagnostics: readonly Diagnostic[];
  expansions: number; visibilityVertices: number;
}>;

/** A small set of stable sequential route orders, scored as complete graphs.
 * Existing channels are treated as noncoincident runs; the search may cross
 * them and pays a nonnegative penalty. Invalid candidates are discarded whole. */
export function routeOrthogonalCandidates(graph: ProperGraph, placement: CorridorPlacement, baseline: GraphGeometry, profile: LayoutProfile = DEFAULT_PROFILE, options: { orders?: number; ripUpMoves?: number } = {}): OrthogonalCandidateResult {
  const candidates: GraphGeometry[] = [], diagnostics: Diagnostic[] = [];
  let totalExpansions = 0, totalVertices = 0;
  const portIndex = new Map(placement.ports.map((port) => [port.id, port]));
  const reference = graph.source.edges.map((_, i) => protectedEdgeSections(graph, placement, i, profile, portIndex));
  const endpoints = (segmentIndex: number): readonly [Point, Point] => {
    const segment = graph.segments[segmentIndex]!, band = placement.bands[graph.vertices[segment.source]!.rank]!;
    const section = reference[segment.edgeIndex]!.find((s) => s.role === "rank-corridor")!;
    return [{ x: segment.sourcePortId ? section.points[0]!.x : placement.x[segment.source]!, y: band.bottom },
      { x: segment.targetPortId ? section.points.at(-1)!.x : placement.x[segment.target]!, y: band.top }];
  };
  const assemble = (routes: ReadonlyMap<number, readonly Point[]>, name: string): GraphGeometry => {
    const edges = graph.source.edges.map((edge, edgeIndex) => ({ id: edge.id, sections: reference[edgeIndex]!.map((section) => {
      if (section.role !== "rank-corridor") return section;
      const points: Point[] = [section.points[0]!], chain = graph.chains[edgeIndex]!;
      for (let i = 0; i + 1 < chain.length; i++) {
        const segment = graph.outgoing[chain[i]!]!.find((index) => graph.segments[index]!.edgeIndex === edgeIndex)!;
        points.push(...routes.get(segment)!);
      }
      points.push(section.points.at(-1)!);
      return { ...section, points: simplifyCollinear(points), commands: undefined };
    }) }));
    return quantizeGeometry({ ...baseline, edges, profileId: `${baseline.profileId}:orthogonal-${name}` });
  };
  const layouts = ["semantic", "reverse", "long-first"].slice(0, options.orders ?? 2);
  for (const name of layouts) {
    const routes = new Map<number, readonly Point[]>();
    let budget = profile.routingExpansions, failed = false;
    for (let rank = 0; rank < graph.segmentsByRank.length && !failed; rank++) {
      const band = placement.bands[rank]!, segmentIds = [...graph.segmentsByRank[rank]!];
      segmentIds.sort((a, b) => {
        if (name === "long-first") { const [as, at] = endpoints(a), [bs, bt] = endpoints(b), difference = Math.abs(bt.x - bs.x) - Math.abs(at.x - as.x); if (difference) return difference; }
        const sign = name === "reverse" ? -1 : 1;
        return sign * compareText(graph.source.edges[graph.segments[a]!.edgeIndex]!.id, graph.source.edges[graph.segments[b]!.edgeIndex]!.id);
      });
      const ends = segmentIds.flatMap((i) => [...endpoints(i)]), xs = ends.map((p) => p.x);
      const low = Math.min(...xs) - profile.portSeparation, high = Math.max(...xs) + profile.portSeparation;
      const interesting = segmentIds.flatMap((id, ordinal) => {
        const [a, b] = endpoints(id), y = band.top + (ordinal + 1) * (band.bottom - band.top) / (segmentIds.length + 1);
        return [{ x: a.x, y }, { x: b.x, y }, { x: (a.x + b.x) / 2, y }];
      });
      const fixed: (readonly Point[])[] = [];
      for (const id of segmentIds) {
        const [start, target] = endpoints(id);
        // Buffer routes at existing bends offers nearby alternative tracks;
        // no segment is ever shifted after attachments/routes were accepted.
        const alternatives = fixed.flatMap((route) => route.flatMap((p) => [
          { x: p.x - profile.portSeparation, y: p.y }, { x: p.x + profile.portSeparation, y: p.y },
        ]));
        const result = orthogonalPath(start, target, { bounds: { x: low, y: band.top, width: high - low, height: band.bottom - band.top },
          interesting: [...interesting, ...alternatives], fixedRoutes: fixed, expansionBudget: budget, visibilityBudget: budget,
          startDirection: "north", targetDirection: "north", bendPenalty: 12, crossingPenalty: 80 });
        totalExpansions += result.expansions; totalVertices += result.visibilityVertices; budget -= result.expansions;
        if (!result.points || result.points.length < 2) { diagnostics.push({ code: `orthogonal-${result.termination}`, message: `Rejected ${name} route candidate without publishing partial geometry`, ids: [graph.source.edges[graph.segments[id]!.edgeIndex]!.id] }); failed = true; break; }
        routes.set(id, result.points); fixed.push(result.points);
      }
    }
    if (failed) continue;
    let geometry = assemble(routes, name), validation = validateGeometry(graph.source, geometry);
    if (!validation.valid) { diagnostics.push({ code: "orthogonal-invalid", message: `${name} candidate rejected by final geometry validator: ${validation.diagnostics.map((d) => d.code).join(", ")}` }); continue; }
    // Bounded rip-up of complete ORIGINAL edges. A dummy segment is never
    // accepted in isolation; full geometry is reassembled and independently
    // scored before a route change can replace the best candidate.
    const pressure = new Array(graph.source.edges.length).fill(0);
    for (const band of graph.segmentsByRank) for (const id of band) {
      const points = routes.get(id)!, fixed = band.filter((other) => other !== id).flatMap((other) => {
        const route = routes.get(other)!; return route.slice(1).map((b, i) => ({ a: route[i]!, b }));
      });
      pressure[graph.segments[id]!.edgeIndex] += points.slice(1).reduce((sum, b, i) => sum + segmentPenalty(points[i]!, b, fixed, 100), 0) + points.length;
    }
    const worst = graph.source.edges.map((_, i) => i).sort((a, b) => pressure[b]! - pressure[a]! || compareText(graph.source.edges[a]!.id, graph.source.edges[b]!.id)).slice(0, options.ripUpMoves ?? 2);
    for (const edgeIndex of worst) {
      if (budget <= 0) break;
      const proposed = new Map(routes), segmentIds = graph.segments.filter((segment) => segment.edgeIndex === edgeIndex).map((segment) => segment.index);
      let complete = true;
      for (const id of segmentIds) {
        const rank = graph.vertices[graph.segments[id]!.source]!.rank, band = placement.bands[rank]!, sameBand = graph.segmentsByRank[rank]!;
        const fixed = sameBand.filter((other) => other !== id).map((other) => routes.get(other)!);
        const [start, target] = endpoints(id), xs = sameBand.flatMap((other) => endpoints(other).map((p) => p.x));
        const low = Math.min(...xs) - profile.portSeparation, high = Math.max(...xs) + profile.portSeparation;
        const interesting = fixed.flatMap((route) => route.flatMap((p) => [p,
          { x: p.x - profile.portSeparation, y: p.y }, { x: p.x + profile.portSeparation, y: p.y },
          { x: p.x, y: p.y - profile.portSeparation }, { x: p.x, y: p.y + profile.portSeparation },
        ]));
        const result = orthogonalPath(start, target, { bounds: { x: low, y: band.top, width: high - low, height: band.bottom - band.top }, fixedRoutes: fixed,
          interesting, startDirection: "north", targetDirection: "north", expansionBudget: budget, visibilityBudget: budget, crossingPenalty: 160 });
        totalExpansions += result.expansions; totalVertices += result.visibilityVertices; budget -= result.expansions;
        if (!result.points || result.points.length < 2) { complete = false; break; }
        proposed.set(id, result.points);
      }
      if (!complete) continue;
      const candidate = assemble(proposed, name), checked = validateGeometry(graph.source, candidate);
      if (!checked.valid) continue;
      const score = (v: typeof validation) => [v.metrics.crossings, v.metrics.repeatedCrossingPairs, v.metrics.tangencies, v.metrics.bends, v.metrics.length];
      const a = score(checked), b = score(validation), different = a.findIndex((value, i) => Math.abs(value - b[i]!) > EPS);
      if (different >= 0 && a[different]! < b[different]!) {
        for (const [id, route] of proposed) routes.set(id, route);
        geometry = candidate; validation = checked;
      }
    }
    candidates.push(geometry);
  }
  return { candidates, diagnostics, expansions: totalExpansions, visibilityVertices: totalVertices };
}
