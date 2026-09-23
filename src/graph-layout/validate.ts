/** Independent final-geometry checks. Deliberately does not import rank,
 * ordering, compaction, routing, or their segment predicates. */
import type { Diagnostic, GraphGeometry, MeasuredGraph, PathCommand, Point, Rect, ValidationResult } from "./types.js";

const EPS = 1e-7;
export const CURVE_DEVIATION = 0.01;
const equal = (a: Point, b: Point, e = EPS) => Math.hypot(a.x - b.x, a.y - b.y) <= e;
const cross = (a: Point, b: Point, c: Point) => (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
const dot = (a: Point, b: Point) => a.x * b.x + a.y * b.y;
const norm = (p: Point) => Math.hypot(p.x, p.y);
const subtract = (a: Point, b: Point) => ({ x: a.x - b.x, y: a.y - b.y });
const finite = (p: Point) => Number.isFinite(p.x) && Number.isFinite(p.y) && Math.abs(p.x) <= 1e9 && Math.abs(p.y) <= 1e9;
const inRect = (p: Point, r: Rect, e = EPS) => p.x >= r.x - e && p.x <= r.x + r.width + e && p.y >= r.y - e && p.y <= r.y + r.height + e;
const grow = (r: Rect, n: number): Rect => ({ x: r.x - n, y: r.y - n, width: r.width + 2 * n, height: r.height + 2 * n });
const placed = (box: Rect, node: Point): Rect => ({ ...box, x: box.x + node.x, y: box.y + node.y });
const overlaps = (a: Rect, b: Rect) => Math.min(a.x + a.width, b.x + b.width) - Math.max(a.x, b.x) > EPS && Math.min(a.y + a.height, b.y + b.height) - Math.max(a.y, b.y) > EPS;
const rectIntersects = (a: Rect, b: Rect) => a.x <= b.x + b.width + EPS && b.x <= a.x + a.width + EPS && a.y <= b.y + b.height + EPS && b.y <= a.y + a.height + EPS;

/** Liang–Barsky clipping, independent of routing's obstacle tests. */
export function segmentHitsRect(a: Point, b: Point, rect: Rect): boolean {
  let low = 0, high = 1;
  for (const [origin, delta, minimum, maximum] of [
    [a.x, b.x - a.x, rect.x, rect.x + rect.width],
    [a.y, b.y - a.y, rect.y, rect.y + rect.height],
  ] as const) {
    if (Math.abs(delta) < EPS) { if (origin < minimum - EPS || origin > maximum + EPS) return false; }
    else {
      const lo = (minimum - origin) / delta, hi = (maximum - origin) / delta;
      low = Math.max(low, Math.min(lo, hi)); high = Math.min(high, Math.max(lo, hi));
      if (low > high + EPS) return false;
    }
  }
  return low <= high + EPS;
}

type Intersection = { kind: "point"; p: Point } | { kind: "overlap"; a: Point; b: Point };
export function segmentIntersection(a: Point, b: Point, c: Point, d: Point): Intersection | undefined {
  const ab = subtract(b, a), cd = subtract(d, c), ca = subtract(c, a);
  const denominator = ab.x * cd.y - ab.y * cd.x;
  if (Math.abs(denominator) > EPS) {
    const t = (ca.x * cd.y - ca.y * cd.x) / denominator;
    const u = (ca.x * ab.y - ca.y * ab.x) / denominator;
    if (t < -EPS || t > 1 + EPS || u < -EPS || u > 1 + EPS) return undefined;
    return { kind: "point", p: { x: a.x + t * ab.x, y: a.y + t * ab.y } };
  }
  if (Math.abs(cross(a, b, c)) > EPS) return undefined;
  const length2 = dot(ab, ab);
  if (length2 < EPS * EPS) {
    if (Math.abs(cross(c, d, a)) <= EPS && inRect(a, { x: Math.min(c.x, d.x), y: Math.min(c.y, d.y), width: Math.abs(d.x - c.x), height: Math.abs(d.y - c.y) })) return { kind: "point", p: a };
    return undefined;
  }
  const t1 = dot(ca, ab) / length2, t2 = dot(subtract(d, a), ab) / length2;
  const lo = Math.max(0, Math.min(t1, t2)), hi = Math.min(1, Math.max(t1, t2));
  if (lo > hi + EPS) return undefined;
  const p = { x: a.x + lo * ab.x, y: a.y + lo * ab.y }, q = { x: a.x + hi * ab.x, y: a.y + hi * ab.y };
  return equal(p, q) ? { kind: "point", p } : { kind: "overlap", a: p, b: q };
}

/** Adaptive de Casteljau flattening. Control-hull distance to the finite
 * chord bounds the deviation of the ENTIRE curve, not a few samples. */
export function flattenCommands(commands: readonly PathCommand[], tolerance = CURVE_DEVIATION): Point[] {
  const out: Point[] = [];
  let previous: Point | undefined;
  for (const command of commands) {
    if (!finite(command.p) || (command.kind === "Q" && !finite(command.control))) throw new Error("nonfinite curve");
    if (command.kind === "M") {
      if (out.length) throw new Error("disconnected curve subpath");
      out.push(command.p);
    } else if (!previous) throw new Error("curve lacks an initial move");
    else if (command.kind === "L") { if (!equal(previous, command.p)) out.push(command.p); }
    else if (command.kind === "Q") {
      const pending: { a: Point; c: Point; b: Point; depth: number }[] = [{ a: previous, c: command.control, b: command.p, depth: 0 }];
      while (pending.length) {
        const { a, c, b, depth } = pending.pop()!;
        const v = subtract(b, a), length2 = dot(v, v);
        const t = length2 ? Math.max(0, Math.min(1, dot(subtract(c, a), v) / length2)) : 0;
        const deviation = Math.hypot(c.x - a.x - t * v.x, c.y - a.y - t * v.y);
        if (deviation <= tolerance) { if (!equal(out[out.length - 1]!, b)) out.push(b); }
        else {
          if (depth >= 24 || out.length + pending.length > 100_000) throw new Error("curve flattening budget exhausted");
          const ac = { x: (a.x + c.x) / 2, y: (a.y + c.y) / 2 }, cb = { x: (c.x + b.x) / 2, y: (c.y + b.y) / 2 };
          const middle = { x: (ac.x + cb.x) / 2, y: (ac.y + cb.y) / 2 };
          pending.push({ a: middle, c: cb, b, depth: depth + 1 }, { a, c: ac, b: middle, depth: depth + 1 });
        }
      }
    } else throw new Error("unsupported curve command");
    previous = command.p;
  }
  return out;
}

/** Read our deliberately small SVG path language back AFTER serialization. */
export function parsePathData(source: string): PathCommand[] {
  const tokens = source.match(/[MLQ]|[-+]?(?:\d*\.\d+|\d+\.?\d*)(?:[eE][-+]?\d+)?/g) ?? [];
  if (source.replace(/[MLQ]|[-+]?(?:\d*\.\d+|\d+\.?\d*)(?:[eE][-+]?\d+)?|[\s,]/g, "")) throw new Error("unsupported SVG path syntax");
  let i = 0;
  const point = (): Point => {
    const x = Number(tokens[i++]), y = Number(tokens[i++]);
    if (!Number.isFinite(x) || !Number.isFinite(y)) throw new Error("malformed SVG coordinate");
    return { x, y };
  };
  const out: PathCommand[] = [];
  while (i < tokens.length) {
    const kind = tokens[i++];
    if (kind === "Q") out.push({ kind, control: point(), p: point() });
    else if (kind === "M" || kind === "L") out.push({ kind, p: point() });
    else throw new Error("missing SVG command");
  }
  return out;
}

type Polyline = { id: string; points: Point[]; source: string; target: string; sourcePort: string; targetPort: string };
type Segment = { route: number; index: number; a: Point; b: Point; minX: number; maxX: number; minY: number; maxY: number };
const pointKey = (p: Point) => `${Math.round(p.x * 1e5)},${Math.round(p.y * 1e5)}`;

/** Geometric turns, not tessellation vertices: one curved corner contributes
 * once, while straight joins of a line and its tangent arc contribute zero. */
export function commandBends(commands: readonly PathCommand[]): number {
  let previous: Point | undefined, tangent: Point | undefined, count = 0;
  const turns = (a: Point, b: Point) => Math.abs(a.x * b.y - a.y * b.x) > 1e-7 * Math.max(1, norm(a) * norm(b)) || dot(a, b) < -EPS;
  for (const command of commands) {
    if (command.kind === "M") { previous = command.p; tangent = undefined; continue; }
    if (!previous) continue;
    const chord = subtract(command.p, previous);
    if (command.kind === "L") {
      if (norm(chord) > EPS) { if (tangent && turns(tangent, chord)) count++; tangent = chord; }
    } else if (command.kind === "Q") {
      let incoming = subtract(command.control, previous), outgoing = subtract(command.p, command.control);
      if (norm(incoming) < EPS) incoming = chord;
      if (norm(outgoing) < EPS) outgoing = chord;
      if (tangent && norm(incoming) > EPS && turns(tangent, incoming)) count++;
      if (norm(incoming) > EPS && norm(outgoing) > EPS && turns(incoming, outgoing)) count++;
      if (norm(outgoing) > EPS) tangent = outgoing;
    }
    previous = command.p;
  }
  return count;
}

function routeSelfIntersection(points: readonly Point[], closedAtSemanticPort: boolean): boolean {
  // A vertically monotone route can revisit itself only within one horizontal
  // plateau. Check those plateaus linearly, avoiding quadratic work on long
  // proper-layer chains. Feedback gets the unrestricted independent check.
  const upward = points.every((p, i) => !i || p.y <= points[i - 1]!.y + EPS);
  const downward = points.every((p, i) => !i || p.y >= points[i - 1]!.y - EPS);
  if (upward || downward) {
    let direction = 0;
    for (let i = 1; i < points.length; i++) {
      const a = points[i - 1]!, b = points[i]!;
      if (Math.abs(b.y - a.y) > EPS) { direction = 0; continue; }
      const step = Math.sign(b.x - a.x);
      if (step && direction && step !== direction) return true;
      if (step) direction = step;
    }
    return false;
  }
  const segments = points.slice(1).map((b, index) => ({ a: points[index]!, b, index })).filter((s) => !equal(s.a, s.b));
  for (let i = 0; i < segments.length; i++) for (let j = i + 1; j < segments.length; j++) {
    const a = segments[i]!, b = segments[j]!, intersection = segmentIntersection(a.a, a.b, b.a, b.b);
    if (!intersection) continue;
    if (intersection.kind === "overlap") return true;
    if (j === i + 1 && equal(intersection.p, a.b) && equal(intersection.p, b.a)) continue;
    if (closedAtSemanticPort && i === 0 && j + 1 === segments.length && equal(intersection.p, points[0]!) && equal(intersection.p, points.at(-1)!)) continue;
    return true;
  }
  return false;
}

function terminalRun(points: readonly Point[], fromStart: boolean): { vector: Point; length: number } {
  const ordered = fromStart ? points : [...points].reverse(), start = ordered[0]!;
  const first = ordered.find((p) => !equal(p, start));
  if (!first) return { vector: { x: 0, y: 0 }, length: 0 };
  const vector = subtract(first, start), length = norm(vector), unit = { x: vector.x / length, y: vector.y / length };
  let distance = 0;
  for (let i = 1; i < ordered.length; i++) {
    const step = subtract(ordered[i]!, ordered[i - 1]!);
    if (Math.abs(step.x * unit.y - step.y * unit.x) > 1e-6 || dot(step, unit) < -EPS) break;
    distance += dot(step, unit);
  }
  return { vector: unit, length: distance };
}

/** Exact command tangents and straight terminal length. An almost-straight
 * quadratic cannot become a fictitious straight arrow stub after flattening. */
function terminalCommandRun(commands: readonly PathCommand[], fromStart: boolean): { vector: Point; length: number } {
  const segments: { a: Point; b: Point; control?: Point }[] = [];
  let previous: Point | undefined;
  for (const command of commands) {
    if (command.kind !== "M" && previous) segments.push({ a: previous, b: command.p, ...(command.kind === "Q" ? { control: command.control } : {}) });
    previous = command.p;
  }
  const ordered = (fromStart ? segments : [...segments].reverse().map((s) => ({ ...s, a: s.b, b: s.a }))).filter((s) => !equal(s.a, s.b) || (s.control && !equal(s.a, s.control)));
  const first = ordered[0];
  if (!first) return { vector: { x: 0, y: 0 }, length: 0 };
  const tangent = subtract(first.control && !equal(first.control, first.a) ? first.control : first.b, first.a), magnitude = norm(tangent);
  const unit = { x: tangent.x / magnitude, y: tangent.y / magnitude };
  let length = 0;
  for (const segment of ordered) {
    const steps = segment.control ? [subtract(segment.control, segment.a), subtract(segment.b, segment.control)] : [subtract(segment.b, segment.a)];
    if (steps.some((step) => Math.abs(step.x * unit.y - step.y * unit.x) > EPS || dot(step, unit) < -EPS)) break;
    length += steps.reduce((sum, step) => sum + dot(step, unit), 0);
  }
  return { vector: unit, length };
}

/** Crossing event classification uses the complete pair of polylines. A bend
 * endpoint may be a proper crossing, while a touched interior may be tangent. */
function raysAt(points: readonly Point[], p: Point): Point[] {
  const rays: Point[] = [];
  for (let i = 1; i < points.length; i++) {
    const a = points[i - 1]!, b = points[i]!;
    if (Math.abs(cross(a, b, p)) > 1e-5 || !inRect(p, { x: Math.min(a.x, b.x), y: Math.min(a.y, b.y), width: Math.abs(a.x - b.x), height: Math.abs(a.y - b.y) }, 1e-5)) continue;
    for (const end of [a, b]) if (!equal(end, p, 1e-5)) {
      const v = subtract(end, p), length = norm(v), ray = { x: v.x / length, y: v.y / length };
      if (!rays.some((other) => equal(ray, other, 1e-5))) rays.push(ray);
    }
  }
  return rays;
}

export function routeMetrics(routes: readonly Polyline[], bounds: Rect) {
  const segments: Segment[] = [];
  let length = 0, bends = 0;
  routes.forEach((route, ri) => route.points.forEach((b, i) => {
    if (!i) return;
    const a = route.points[i - 1]!;
    length += Math.hypot(b.x - a.x, b.y - a.y);
    if (i > 1 && Math.abs(cross(route.points[i - 2]!, a, b)) > EPS) bends++;
    if (!equal(a, b)) segments.push({ route: ri, index: i - 1, a, b, minX: Math.min(a.x, b.x), maxX: Math.max(a.x, b.x), minY: Math.min(a.y, b.y), maxY: Math.max(a.y, b.y) });
  }));
  segments.sort((a, b) => a.minX - b.minX || a.route - b.route || a.index - b.index);
  const events = new Map<string, { a: number; b: number; p: Point }>();
  const overlapPairs = new Set<string>();
  for (let i = 0; i < segments.length; i++) {
    const a = segments[i]!;
    for (let j = i + 1; j < segments.length; j++) {
      const b = segments[j]!;
      if (b.minX > a.maxX + EPS) break;
      if (a.route === b.route || a.maxY < b.minY - EPS || b.maxY < a.minY - EPS) continue;
      const intersection = segmentIntersection(a.a, a.b, b.a, b.b);
      if (!intersection) continue;
      const left = Math.min(a.route, b.route), right = Math.max(a.route, b.route), key = `${left}:${right}`;
      // Several visual dependencies may deliberately leave one declared
      // source port as a common trunk before branching. Only that explicit
      // source-port junction exempts their coincident run; shared targets and
      // unrelated ports remain hard overlap defects.
      if (intersection.kind === "overlap") {
        if (routes[left]!.sourcePort !== routes[right]!.sourcePort) overlapPairs.add(key);
        continue;
      }
      const ra = routes[a.route]!, rb = routes[b.route]!, p = intersection.p;
      // Only an ACTUAL shared semantic port is exempted, at that point.
      const endsA = [[ra.sourcePort, ra.points[0]!], [ra.targetPort, ra.points.at(-1)!]] as const;
      const endsB = [[rb.sourcePort, rb.points[0]!], [rb.targetPort, rb.points.at(-1)!]] as const;
      if (endsA.some(([pa, ap]) => endsB.some(([pb, bp]) => pa === pb && equal(ap, p, 1e-5) && equal(bp, p, 1e-5)))) continue;
      events.set(`${key}:${pointKey(p)}`, { a: left, b: right, p });
    }
  }
  let crossings = 0, endpointTouches = 0, tangencies = 0, minimumAngle = Infinity;
  const pairs = new Map<string, number>(), sites = new Map<string, Set<number>>();
  for (const { a, b, p } of events.values()) {
    const ra = raysAt(routes[a]!.points, p), rb = raysAt(routes[b]!.points, p);
    if (ra.length < 2 || rb.length < 2) { endpointTouches++; continue; }
    const sorted = [...ra.map((r) => ({ ...r, owner: 0 })), ...rb.map((r) => ({ ...r, owner: 1 }))].sort((x, y) => Math.atan2(x.y, x.x) - Math.atan2(y.y, y.x));
    const proper = sorted.length === 4 && sorted.every((ray, i) => ray.owner !== sorted[(i + 1) % 4]!.owner && !equal(ray, sorted[(i + 1) % 4]!, 1e-5));
    if (!proper) { tangencies++; continue; }
    crossings++;
    const key = `${a}:${b}`; pairs.set(key, (pairs.get(key) ?? 0) + 1);
    const site = sites.get(pointKey(p)) ?? new Set<number>(); site.add(a); site.add(b); sites.set(pointKey(p), site);
    for (const x of ra) for (const y of rb) minimumAngle = Math.min(minimumAngle, Math.acos(Math.min(1, Math.abs(dot(x, y)))) * 180 / Math.PI);
  }
  return { crossings, repeatedCrossingPairs: [...pairs.values()].filter((n) => n > 1).length,
    endpointTouches, tangencies, multiwayCrossings: [...sites.values()].filter((ids) => ids.size > 2).length,
    overlaps: overlapPairs.size, bends, length, width: bounds.width, height: bounds.height,
    minimumCrossingAngle: Number.isFinite(minimumAngle) ? minimumAngle : null };
}

function validateSurface(graph: MeasuredGraph, geometry: GraphGeometry, surface: "reference" | "rendered"): ValidationResult {
  const diagnostics: Diagnostic[] = [];
  const fail = (code: string, message: string, ...ids: string[]) => diagnostics.push({ code, message, ids });
  const empty = () => ({ valid: false, diagnostics, metrics: routeMetrics([], { x: 0, y: 0, width: 0, height: 0 }) });
  if (!geometry || geometry.schemaVersion !== 1 || !Array.isArray(geometry.nodes) || !Array.isArray(geometry.ports) || !Array.isArray(geometry.edges)) {
    fail("geometry-schema", "Missing or unsupported complete geometry schema"); return empty();
  }
  const rectValid = (r: Rect) => r && finite(r) && Number.isFinite(r.width) && Number.isFinite(r.height) && r.width >= 0 && r.height >= 0;
  if (!rectValid(geometry.bounds)) { fail("nonfinite-bounds", "Invalid diagram extent"); return empty(); }
  const nodes = new Map<string, GraphGeometry["nodes"][number]>(geometry.nodes.map((node) => [node.id, node]));
  const ports = new Map<string, GraphGeometry["ports"][number]>(geometry.ports.map((port) => [port.id, port]));
  const specs = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const edges = new Map<string, GraphGeometry["edges"][number]>(geometry.edges.map((edge) => [edge.id, edge]));
  if (nodes.size !== geometry.nodes.length || nodes.size !== graph.nodes.length) fail("node-roundtrip", "Node multiplicity changed");
  if (ports.size !== geometry.ports.length || ports.size !== specs.size) fail("port-roundtrip", "Port multiplicity changed");
  if (edges.size !== geometry.edges.length || edges.size !== graph.edges.length) fail("edge-roundtrip", "Edge multiplicity changed");
  for (const node of graph.nodes) {
    const position = nodes.get(node.id);
    if (!position) { fail("missing-node", "Measured node is absent", node.id); continue; }
    if (!rectValid(position) || Math.abs(position.width - node.width) > 0.0011 || Math.abs(position.height - node.height) > 0.0011) fail("node-size", "Node size changed or is nonfinite", node.id);
    if (position.rank !== undefined && (!Number.isSafeInteger(position.rank) || position.rank < 0)) fail("invalid-rank", "An emitted rank is not a nonnegative safe integer", node.id);
    if (!inRect(position, geometry.bounds) || !inRect({ x: position.x + position.width, y: position.y + position.height }, geometry.bounds, 0.002)) fail("node-bounds", "Node lies outside diagram", node.id);
    for (const spec of node.ports) {
      const port = ports.get(spec.id);
      if (!port) { fail("missing-port", "Port is absent", spec.id); continue; }
      if (!finite(port) || port.nodeId !== node.id) { fail("port-owner", "Invalid coordinate or wrong port owner", spec.id); continue; }
      if (spec.mode === "fixed-position" && spec.offset) {
        if (!equal(port, { x: position.x + spec.offset.x, y: position.y + spec.offset.y }, 0.002)) fail("fixed-port", "Fixed attachment moved", spec.id);
      } else {
        const side = spec.side === "north" ? port.y - position.y : spec.side === "south" ? port.y - position.y - position.height : spec.side === "west" ? port.x - position.x : port.x - position.x - position.width;
        if (Math.abs(side) > 0.002 || !inRect(port, position, 0.002)) fail("port-side", "Attachment does not lie on its declared side", spec.id);
        if (spec.mode === "free-in-slots" && !node.ports.some((slot) => slot.mode === "free-in-slots" && slot.side === spec.side && slot.offset &&
          equal(port, { x: position.x + slot.offset.x, y: position.y + slot.offset.y }, 0.002)))
          fail("port-slot", "Attachment left its measured slot pool", spec.id);
      }
    }
    for (const side of ["north", "south", "east", "west"]) {
      const fixed = node.ports.filter((p) => p.side === side && p.mode === "fixed-order").sort((a, b) => a.order! - b.order!);
      for (let i = 1; i < fixed.length; i++) {
        const a = ports.get(fixed[i - 1]!.id), b = ports.get(fixed[i]!.id);
        if (!a || !b) continue;
        if ((side === "north" || side === "south" ? a.x > b.x + EPS : a.y > b.y + EPS)) fail("port-order", "A fixed attachment order changed", fixed[i - 1]!.id, fixed[i]!.id);
      }
    }
  }
  if (diagnostics.some((d) => ["node-size", "port-owner", "missing-node", "missing-port"].includes(d.code))) return empty();
  for (let i = 0; i < geometry.nodes.length; i++) for (let j = i + 1; j < geometry.nodes.length; j++) {
    const a = geometry.nodes[i]!, b = geometry.nodes[j]!;
    if (overlaps(a, b)) fail("node-overlap", "Measured node envelopes overlap", a.id, b.id);
  }
  const groups = new Map((geometry.groups ?? []).map((group) => [group.id, group]));
  if (groups.size !== (geometry.groups ?? []).length) fail("group-identity", "Duplicate display group identity");
  const verifiedGroups = new Set<string>(), memberships = new Map<string, Set<string>>();
  const allGates = new Set<string>();
  for (const node of nodes.values()) if (node.parentId && (!groups.has(node.parentId) || !groups.get(node.parentId)!.memberIds.includes(node.id))) fail("group-parent", "Node parent does not name a containing group", node.id, node.parentId);
  for (const group of groups.values()) {
    if (!rectValid(group)) { fail("group-bounds", "Nonfinite group", group.id); continue; }
    const members = new Set(group.memberIds);
    memberships.set(group.id, members);
    if (!members.size || members.size !== group.memberIds.length) fail("group-members", "A display group has no members or repeats a member", group.id);
    if (!inRect(group, geometry.bounds) || !inRect({ x: group.x + group.width, y: group.y + group.height }, geometry.bounds, 0.002)) fail("group-bounds", "Display group lies outside the drawing", group.id);
    for (const label of group.labelBoxes) if (!rectValid(label) || !inRect(label, { x: 0, y: 0, width: group.width, height: group.height }) || !inRect({ x: label.x + label.width, y: label.y + label.height }, { x: 0, y: 0, width: group.width, height: group.height })) fail("group-label", "Group label is nonfinite or leaves its measured envelope", group.id);
    for (const id of members) {
      const node = nodes.get(id);
      if (!node || node.parentId !== group.id || !inRect(node, group) || !inRect({ x: node.x + node.width, y: node.y + node.height }, group)) fail("group-containment", "Group membership/containment is inconsistent", group.id, id);
    }
    for (const node of geometry.nodes) if (!members.has(node.id) && overlaps(group, node)) fail("group-overlap", "A group obstructs an unrelated node", group.id, node.id);
    // Independent reachability proves this is a displayed SCC, not just a
    // router-created excuse to permit arbitrary backward ordinary edges.
    // Forward AND reverse reachability from one member proves strong
    // connectivity, independently of the layout's SCC helper, in linear work.
    const forward = new Map([...members].map((id) => [id, [] as string[]])), reverse = new Map([...members].map((id) => [id, [] as string[]]));
    for (const edge of graph.edges) {
      const a = specs.get(edge.sourcePortId)?.nodeId, b = specs.get(edge.targetPortId)?.nodeId;
      if (a && b && members.has(a) && members.has(b)) { forward.get(a)!.push(b); reverse.get(b)!.push(a); }
    }
    const start = members.values().next().value as string | undefined;
    const reachesAll = (adjacency: Map<string, string[]>) => {
      if (start === undefined) return false;
      const reached = new Set([start]), queue = [start];
      for (let i = 0; i < queue.length; i++) for (const next of adjacency.get(queue[i]!) ?? []) if (!reached.has(next)) { reached.add(next); queue.push(next); }
      return reached.size === members.size;
    };
    if (!reachesAll(forward) || !reachesAll(reverse)) fail("invalid-scc", "Displayed group is not strongly connected", group.id);
    else verifiedGroups.add(group.id);
    const edgeGates = new Set<string>();
    for (const gate of group.gates ?? []) {
      if (allGates.has(gate.id)) fail("gate-identity", "Duplicate boundary gate identity", group.id, gate.id);
      allGates.add(gate.id);
      if (edgeGates.has(gate.edgeId)) fail("gate-incidence", "An external incidence has more than one gate on one group", group.id, gate.edgeId);
      edgeGates.add(gate.edgeId);
      const edge = graph.edges.find((e) => e.id === gate.edgeId), source = edge && specs.get(edge.sourcePortId), target = edge && specs.get(edge.targetPortId);
      if (!source || !target || members.has(source.nodeId) === members.has(target.nodeId)) fail("gate-incidence", "Gate does not belong to an external incidence of its group", group.id, gate.id);
      const side = gate.side === "north" ? gate.point.y - group.y : gate.side === "south" ? gate.point.y - group.y - group.height : gate.side === "west" ? gate.point.x - group.x : gate.side === "east" ? gate.point.x - group.x - group.width : Infinity;
      if (!finite(gate.point) || Math.abs(side) > 0.002 || !inRect(gate.point, group, 0.002)) fail("gate-boundary", "Gate is not on its declared group boundary", group.id, gate.id);
    }
  }
  const groupList = [...groups.values()];
  for (let i = 0; i < groupList.length; i++) for (let j = i + 1; j < groupList.length; j++) if (overlaps(groupList[i]!, groupList[j]!)) fail("group-overlap", "Distinct display group envelopes overlap", groupList[i]!.id, groupList[j]!.id);
  const obstacles = graph.nodes.flatMap((node) => {
    const at = nodes.get(node.id)!;
    return [
      ...(node.footprints ?? [{ id: node.id, kind: "body" as const, bounds: { x: 0, y: 0, width: node.width, height: node.height } }]).map((f) => ({ owner: node.id, semantic: f.semanticEndpointId, kind: f.kind, id: f.id, box: placed(f.bounds, at) })),
      ...node.labelBoxes.map((r, i) => ({ owner: node.id, semantic: undefined, kind: "label", id: `${node.id}:label:${i}`, box: placed(r, at) })),
    ];
  });
  for (const group of groups.values()) group.labelBoxes.forEach((box, i) => obstacles.push({ owner: group.id, semantic: undefined, kind: "label", id: `${group.id}:label:${i}`, box: placed(box, group) }));
  const routes: Polyline[] = [], arrowheads: { owner: string; targetNode: string; targetSemantic: string; box: Rect }[] = [];
  const allSections = new Set<string>();
  let geometricBends = 0;
  for (const edge of graph.edges) {
    const output = edges.get(edge.id), source = specs.get(edge.sourcePortId), target = specs.get(edge.targetPortId);
    const start = ports.get(edge.sourcePortId), end = ports.get(edge.targetPortId);
    if (!output || !source || !target || !start || !end) { fail("missing-edge", "Incidence or endpoint is absent", edge.id); continue; }
    const sourceNode = nodes.get(source.nodeId)!, targetNode = nodes.get(target.nodeId)!;
    const commonGroup = sourceNode.parentId && sourceNode.parentId === targetNode.parentId && verifiedGroups.has(sourceNode.parentId) ? sourceNode.parentId : undefined;
    if (!commonGroup && sourceNode.rank !== undefined && targetNode.rank !== undefined && targetNode.rank - sourceNode.rank < edge.minRankSpan) fail("rank-feasibility", "Emitted ranks violate the edge's minimum span", edge.id);
    const sections = new Map(output.sections.map((s) => [s.id, s]));
    if (!sections.size || sections.size !== output.sections.length) { fail("section-identity", "Missing or duplicate route section", edge.id); continue; }
    for (const section of output.sections) {
      if (allSections.has(section.id)) fail("section-identity", "A route section identity is reused across edges", edge.id, section.id);
      allSections.add(section.id);
    }
    const incoming = new Set(output.sections.flatMap((s) => [...s.nextSectionIds]));
    const first = output.sections.filter((s) => !incoming.has(s.id));
    if (first.length !== 1) { fail("section-topology", "Route needs one connected origin", edge.id); continue; }
    let current = first[0]; const visited = new Set<string>(); const points: Point[] = [], joins: Point[] = [], commands: PathCommand[] = [];
    while (current) {
      if (visited.has(current.id)) { fail("section-cycle", "Route-section topology is cyclic", edge.id); break; }
      visited.add(current.id);
      if (current.points.length < 2 || !current.points.every(finite)) { fail("nonfinite-route", "Route section needs finite endpoints", edge.id); break; }
      let flat = [...current.points];
      if (surface === "rendered" && current.commands) {
        try {
          flat = flattenCommands(current.commands);
          if (flat.length < 2 || !equal(flat[0]!, current.points[0]!, 0.002) || !equal(flat.at(-1)!, current.points.at(-1)!, 0.002)) fail("curve-attachments", "Curve endpoints changed", edge.id);
        } catch (error) { fail("invalid-curve", String(error), edge.id); break; }
      }
      const sectionCommands = surface === "rendered" && current.commands ? current.commands : current.points.map((p, i) => ({ kind: i ? "L" as const : "M" as const, p }));
      commands.push(...(commands.length ? sectionCommands.slice(1) : sectionCommands));
      const role = current.role ?? "rank-corridor";
      if (!["rank-corridor", "terminal-adapter", "group-adapter", "feedback"].includes(role)) fail("route-role", "Unknown route role", edge.id, current.id);
      if (role === "feedback" && !commonGroup) fail("feedback-outside-scc", "Backward route is outside a displayed SCC", edge.id);
      if (role === "feedback" && commonGroup && !flat.every((p) => inRect(p, groups.get(commonGroup)!, 0.002))) fail("feedback-containment", "An internal feedback route leaves its displayed SCC", edge.id, commonGroup);
      if (role === "terminal-adapter") {
        const node = current === first[0] ? nodes.get(source.nodeId)! : !current.nextSectionIds.length ? nodes.get(target.nodeId)! : undefined;
        if (!node || !flat.every((p) => inRect(p, grow(node, 24)))) fail("invalid-terminal-adapter", "Terminal adapter escapes its documented node neighbourhood", edge.id);
      }
      if (role === "group-adapter") {
        const possible = [nodes.get(source.nodeId)!.parentId, nodes.get(target.nodeId)!.parentId].flatMap((id) => id && groups.has(id) ? [groups.get(id)!] : []);
        if (!possible.some((group) => flat.every((p) => inRect(p, grow(group, 16))))) fail("invalid-group-adapter", "Boundary adapter escapes its group", edge.id);
      }
      if (role === "rank-corridor") for (let i = 1; i < flat.length; i++) if (flat[i]!.y > flat[i - 1]!.y + EPS) fail("reverse-flow", "Ordinary dependency route moves downward", edge.id);
      if (surface === "rendered" && current.commands) {
        let previous: Point | undefined;
        for (const command of current.commands) {
          if (!inRect(command.p, geometry.bounds, 0.002) || (command.kind === "Q" && !inRect(command.control, geometry.bounds, 0.002))) fail("curve-bounds", "Curve control hull escapes the diagram", edge.id);
          if (command.kind === "Q" && previous) {
            if (role === "rank-corridor" && (command.control.y > previous.y + EPS || command.p.y > command.control.y + EPS)) fail("reverse-flow", "An ordinary quadratic has a backward derivative", edge.id);
            if (role === "feedback" && commonGroup && !inRect(command.control, groups.get(commonGroup)!, 0.002)) fail("feedback-containment", "Feedback curve control hull escapes its group", edge.id, commonGroup);
            if (role === "terminal-adapter") {
              const owner = current === first[0] ? sourceNode : !current.nextSectionIds.length ? targetNode : undefined;
              if (!owner || !inRect(command.control, grow(owner, 24))) fail("invalid-terminal-adapter", "Terminal curve control hull escapes its documented neighborhood", edge.id);
            }
            if (role === "group-adapter") {
              const possible = [sourceNode.parentId, targetNode.parentId].flatMap((id) => id && groups.has(id) ? [groups.get(id)!] : []);
              if (!possible.some((group) => inRect(command.control, grow(group, 16)))) fail("invalid-group-adapter", "Group curve control hull escapes its documented neighborhood", edge.id);
            }
          }
          previous = command.p;
        }
      }
      if (points.length) {
        joins.push(flat[0]!);
        if (!equal(points.at(-1)!, flat[0]!, 0.002)) fail("disconnected-section", "Route sections do not meet", edge.id, current.id);
      }
      points.push(...(points.length ? flat.slice(1) : flat));
      if (!current.nextSectionIds.length && current.terminalTargetPortId !== target.id) fail("terminal-marker", "Marker does not belong to the semantic target", edge.id);
      if (current.nextSectionIds.length && current.terminalTargetPortId) fail("boundary-marker", "Arrowhead is incorrectly placed at a section boundary", edge.id);
      if (current.nextSectionIds.length > 1) { fail("implicit-junction", "An incidence cannot silently branch or share a stem", edge.id); break; }
      const next = current.nextSectionIds[0];
      if (next && !sections.has(next)) fail("missing-section", "Section names an absent successor", edge.id, next);
      current = next ? sections.get(next) : undefined;
    }
    if (visited.size !== sections.size) fail("lost-section", "Route contains unreachable sections", edge.id);
    if (points.length < 2) continue;
    geometricBends += commandBends(commands);
    if (!equal(points[0]!, start, 0.002) || !equal(points.at(-1)!, end, 0.002)) fail("wrong-attachment", "Route does not meet its semantic ports", edge.id);
    if (!points.every((p) => inRect(p, geometry.bounds, 0.002))) fail("route-bounds", "Route escapes the diagram extent", edge.id);
    const route: Polyline = { id: edge.id, points, source: source.nodeId, target: target.nodeId, sourcePort: source.id, targetPort: target.id };
    routes.push(route);
    const curved = surface === "rendered" && output.sections.some((s) => s.commands?.some((c) => c.kind === "Q"));
    if (routeSelfIntersection(points, source.id === target.id)) fail("route-self-intersection", "An incidence crosses or retraces itself", edge.id);
    const normal = (side: string): Point => side === "north" ? { x: 0, y: -1 } : side === "south" ? { x: 0, y: 1 } : side === "west" ? { x: -1, y: 0 } : { x: 1, y: 0 };
    const leaving = surface === "rendered" ? terminalCommandRun(commands, true) : terminalRun(points, true);
    const entering = surface === "rendered" ? terminalCommandRun(commands, false) : terminalRun(points, false);
    if (leaving.length < EPS || !equal(leaving.vector, normal(source.side), 1e-5)) fail("source-direction", "Route does not leave its source along the declared port normal", edge.id, source.id);
    if (entering.length < 7 - 0.002 || !equal(entering.vector, normal(target.side), 1e-5)) fail("terminal-direction", "Route needs a straight 7px inward approach along its target port normal", edge.id, target.id);
    for (const group of groups.values()) {
      const members = memberships.get(group.id) ?? new Set<string>(), fromInside = members.has(source.nodeId), toInside = members.has(target.nodeId);
      if (!fromInside && !toInside) {
        if (points.some((p, i) => i > 0 && segmentHitsRect(points[i - 1]!, p, grow(group, curved ? CURVE_DEVIATION : 0)))) fail("nonincident-group", "A route crosses an unrelated display group", edge.id, group.id);
        continue;
      }
      if (fromInside && toInside) {
        if (!points.every((p) => inRect(p, group, 0.002))) fail("feedback-containment", "An internal incidence leaves its display group", edge.id, group.id);
        continue;
      }
      const gates = (group.gates ?? []).filter((gate) => gate.edgeId === edge.id);
      if (gates.length !== 1) { fail("missing-gate", "An external incidence requires exactly one boundary gate on its group", edge.id, group.id); continue; }
      const gate = gates[0]!, corners = [{ x: group.x, y: group.y }, { x: group.x + group.width, y: group.y }, { x: group.x + group.width, y: group.y + group.height }, { x: group.x, y: group.y + group.height }];
      const hits = new Map<string, Point>();
      for (let i = 1; i < points.length; i++) for (let side = 0; side < 4; side++) {
        const intersection = segmentIntersection(points[i - 1]!, points[i]!, corners[side]!, corners[(side + 1) % 4]!);
        if (intersection?.kind === "overlap") fail("group-boundary-run", "A route follows a group boundary instead of using its gate", edge.id, group.id);
        else if (intersection) hits.set(pointKey(intersection.p), intersection.p);
      }
      const tolerance = 0.002 + (curved ? CURVE_DEVIATION : 0);
      if (!hits.size || [...hits.values()].some((p) => !equal(p, gate.point, tolerance))) fail("wrong-gate", "Route crosses a group boundary away from its registered gate", edge.id, gate.id);
      if (!joins.some((point) => equal(point, gate.point, 0.002))) fail("gate-section-join", "Group interior and exterior must join explicitly at their registered gate", edge.id, gate.id);
    }
    for (let i = 1; i < points.length; i++) for (const obstacle of obstacles) {
      const incidentNode = obstacle.owner === source.nodeId || obstacle.owner === target.nodeId;
      if (obstacle.kind === "attachment-area" && obstacle.owner === source.nodeId && source.side === "north" &&
        obstacles.some((f) => f.owner === source.nodeId && f.kind === "dock" && f.semantic === source.semanticEndpointId)) continue;
      if (obstacle.kind === "body" && incidentNode && ((obstacle.owner === source.nodeId && i === 1) || (obstacle.owner === target.nodeId && i === points.length - 1))) continue;
      if (obstacle.kind === "dock" && ((obstacle.owner === source.nodeId && obstacle.semantic === source.semanticEndpointId) || (obstacle.owner === target.nodeId && obstacle.semantic === target.semanticEndpointId))) continue;
      if (obstacle.kind === "rail" && incidentNode && ((obstacle.owner === source.nodeId && i === 1) || (obstacle.owner === target.nodeId && i === points.length - 1))) continue;
      if (segmentHitsRect(points[i - 1]!, points[i]!, grow(obstacle.box, curved ? CURVE_DEVIATION : 0))) {
        fail("obstacle-collision", `Edge meets a nonincident ${obstacle.kind}`, edge.id, obstacle.id); break;
      }
    }
    const before = points[points.length - 2]!, v = subtract(end, before), len = norm(v);
    if (len < EPS) fail("terminal-direction", "Arrowhead has no terminal direction", edge.id);
    else {
      const base = { x: end.x - v.x / len * 7, y: end.y - v.y / len * 7 };
      arrowheads.push({ owner: edge.id, targetNode: target.nodeId, targetSemantic: target.semanticEndpointId, box: { x: Math.min(end.x, base.x) - 2.5, y: Math.min(end.y, base.y) - 2.5, width: Math.abs(end.x - base.x) + 5, height: Math.abs(end.y - base.y) + 5 } });
    }
  }
  for (const route of routes) for (const head of arrowheads) {
    if (route.id === head.owner) continue;
    if (route.points.some((p, i) => i && segmentHitsRect(route.points[i - 1]!, p, head.box))) fail("arrowhead-collision", "A distinct route enters an arrowhead exclusion region", route.id, head.owner);
  }
  for (const head of arrowheads) {
    if (!inRect(head.box, geometry.bounds, 0.002) || !inRect({ x: head.box.x + head.box.width, y: head.box.y + head.box.height }, geometry.bounds, 0.002)) fail("arrowhead-bounds", "An arrowhead exclusion region leaves the diagram", head.owner);
    for (const obstacle of obstacles) {
      if (obstacle.owner === head.targetNode && (obstacle.kind === "body" || obstacle.kind === "rail" || (obstacle.kind === "dock" && obstacle.semantic === head.targetSemantic))) continue;
      if (rectIntersects(head.box, obstacle.box)) fail("arrowhead-obstacle", `Arrowhead exclusion region overlaps a nonincident ${obstacle.kind}`, head.owner, obstacle.id);
    }
  }
  for (let i = 0; i < arrowheads.length; i++) for (let j = i + 1; j < arrowheads.length; j++) if (rectIntersects(arrowheads[i]!.box, arrowheads[j]!.box)) fail("arrowhead-overlap", "Distinct arrowhead exclusion regions overlap", arrowheads[i]!.owner, arrowheads[j]!.owner);
  const metrics = { ...routeMetrics(routes, geometry.bounds), bends: geometricBends };
  if (metrics.overlaps) fail("coincident-run", `${metrics.overlaps} distinct edge pairs have positive-length overlap`);
  if (metrics.endpointTouches) fail("nonjunction-touch", `${metrics.endpointTouches} edge contacts are not declared semantic junctions`);
  return { valid: diagnostics.length === 0, diagnostics, metrics };
}

/** Both surfaces are checked: a safe serialized curve cannot conceal an
 * invalid reference corridor, and a safe corridor cannot excuse a bad curve. */
export function validateGeometry(graph: MeasuredGraph, geometry: GraphGeometry): ValidationResult {
  try {
    const reference = validateSurface(graph, geometry, "reference");
    if (!geometry?.edges?.some((edge) => edge.sections?.some((section) => section.commands))) return reference;
    const rendered = validateSurface(graph, geometry, "rendered"), seen = new Set<string>();
    const diagnostics = [...reference.diagnostics, ...rendered.diagnostics].filter((diagnostic) => {
      const key = JSON.stringify(diagnostic); if (seen.has(key)) return false; seen.add(key); return true;
    });
    return { valid: diagnostics.length === 0, diagnostics, metrics: rendered.metrics };
  } catch (error) {
    return { valid: false, diagnostics: [{ code: "geometry-schema", message: `Malformed complete geometry: ${error instanceof Error ? error.message : String(error)}` }], metrics: routeMetrics([], { x: 0, y: 0, width: 0, height: 0 }) };
  }
}
