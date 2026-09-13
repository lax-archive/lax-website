import { QUANTUM, type GraphGeometry, type PathCommand, type Point, type Rect } from "./types.js";

/** Resolve half-grid ties consistently after equivalent coordinate arithmetic
 * (e.g. center - width/2 + width/2). Two floating-point rounding units around
 * a half integer are numerical noise, not an extra geometric clearance. Ties
 * retain Math.round's toward-positive-infinity policy, including negatives. */
export function quantize(n: number): number {
  const scaled = n / QUANTUM, half = Math.floor(scaled) + 0.5;
  const tie = Math.abs(scaled - half) <= 2 * Number.EPSILON * Math.max(1, Math.abs(scaled));
  return Math.round(tie ? half : scaled) * QUANTUM || 0;
}
export const quantizePoint = (p: Point): Point => ({ x: quantize(p.x), y: quantize(p.y) });
export const distance = (a: Point, b: Point): number => Math.hypot(b.x - a.x, b.y - a.y);
export const translateRect = (r: Rect, p: Point): Rect => ({ ...r, x: r.x + p.x, y: r.y + p.y });
export const expandRect = (r: Rect, gap: number): Rect => ({ x: r.x - gap, y: r.y - gap, width: r.width + 2 * gap, height: r.height + 2 * gap });
export const samePoint = (a: Point, b: Point, tolerance = 1e-7): boolean => distance(a, b) <= tolerance;

/** Drop a middle collinear point only if it lies between its neighbours. */
export function simplifyCollinear(input: readonly Point[]): Point[] {
  const out: Point[] = [];
  for (const p of input) {
    if (out.length && samePoint(out[out.length - 1]!, p)) continue;
    while (out.length >= 2) {
      const a = out[out.length - 2]!, b = out[out.length - 1]!;
      const cross = (b.x - a.x) * (p.y - b.y) - (b.y - a.y) * (p.x - b.x);
      const dot = (b.x - a.x) * (p.x - b.x) + (b.y - a.y) * (p.y - b.y);
      if (Math.abs(cross) > 1e-8 || dot < 0) break;
      out.pop();
    }
    out.push(p);
  }
  return out;
}

/** Candidate only: every result must pass the independent curve validator.
 * Adjacent corners share at most half a segment; endpoints stay unchanged. */
export function roundCorners(points: readonly Point[], radius: number): PathCommand[] {
  if (!points.length) return [];
  const out: PathCommand[] = [{ kind: "M", p: points[0]! }];
  for (let i = 1; i < points.length - 1; i++) {
    const a = points[i - 1]!, b = points[i]!, c = points[i + 1]!;
    const ab = distance(a, b), bc = distance(b, c), r = Math.min(radius, ab / 2, bc / 2);
    if (r <= 0) continue;
    const p = { x: b.x + (a.x - b.x) * r / ab, y: b.y + (a.y - b.y) * r / ab };
    const q = { x: b.x + (c.x - b.x) * r / bc, y: b.y + (c.y - b.y) * r / bc };
    out.push({ kind: "L", p }, { kind: "Q", control: b, p: q });
  }
  if (points.length > 1) out.push({ kind: "L", p: points[points.length - 1]! });
  return out;
}
export function pathData(commands: readonly PathCommand[]): string {
  const n = (x: number) => String(Number(x.toFixed(3)));
  return commands.map((command) => command.kind === "Q"
    ? `Q${n(command.control.x)},${n(command.control.y)} ${n(command.p.x)},${n(command.p.y)}`
    : `${command.kind}${n(command.p.x)},${n(command.p.y)}`).join(" ");
}
export function polylineCommands(points: readonly Point[]): PathCommand[] {
  return points.map((p, i) => ({ kind: i ? "L" : "M", p }));
}
export function quantizeGeometry(geometry: GraphGeometry): GraphGeometry {
  const rect = (r: Rect) => ({ x: quantize(r.x), y: quantize(r.y), width: quantize(r.width), height: quantize(r.height) });
  return { ...geometry, bounds: rect(geometry.bounds),
    nodes: geometry.nodes.map((node) => ({ ...node, ...rect(node) })),
    ports: geometry.ports.map((port) => ({ ...port, ...quantizePoint(port) })),
    groups: geometry.groups?.map((group) => ({ ...group, ...rect(group), labelBoxes: group.labelBoxes.map(rect),
      ...(group.gates ? { gates: group.gates.map((gate) => ({ ...gate, point: quantizePoint(gate.point) })) } : {}) })),
    edges: geometry.edges.map((edge) => ({ ...edge, sections: edge.sections.map((section) => ({ ...section,
      points: section.points.map(quantizePoint), commands: section.commands?.map((command) => command.kind === "Q"
        ? { kind: "Q", p: quantizePoint(command.p), control: quantizePoint(command.control) }
        : { kind: command.kind, p: quantizePoint(command.p) }) })) })) };
}
