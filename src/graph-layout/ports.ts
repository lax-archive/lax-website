import { compareText } from "./normalize.js";
import type { PortOrder } from "./proper-graph.js";
import { GraphDiagnosticError, type MeasuredGraph, type MeasuredNode, type PlacedNode, type PlacedPort, type Point, type PortSpec } from "./types.js";

export type PortOffsets = Readonly<Record<string, Point>>;

/** Statement circles below a concept use reserved internal lanes to reach
 * the top boundary without passing through the concept label. Each incidence
 * has its own lane and column; the full route remains independently checked. */
export function belowBodyEscape(measured: MeasuredNode, node: PlacedNode, port: PlacedPort, separation: number, escape = 12): Point[] | undefined {
  const body = measured.footprints?.find((f) => f.kind === "body")?.bounds;
  if (!body || port.y <= node.y + body.y + body.height) return undefined;
  const peers = measured.ports.filter((p) => p.side === "north" && p.offset && p.offset.y > body.y + body.height);
  const lane = peers.findIndex((p) => p.id === port.id);
  if (lane < 0) return undefined;
  const y = node.y + body.y + body.height + escape + lane * separation;
  const x = node.x + body.x - escape - lane * separation;
  return [port, { x: port.x, y }, { x, y }, { x, y: node.y - escape }];
}
const horizontal = (side: PortSpec["side"]) => side === "north" || side === "south";

/** Finalize attachment geometry BEFORE coordinates and routing. Fixed positions
 * are copied exactly; free ports never get reordered by the SVG serializer. */
export function portOffsets(graph: MeasuredGraph, order: PortOrder = {}, separation = 8, endPadding = 8): PortOffsets {
  const result: Record<string, Point> = {};
  for (const node of graph.nodes) for (const side of ["north", "south", "east", "west"] as const) {
    const ports = node.ports.filter((port) => port.side === side);
    const extent = horizontal(side) ? node.width : node.height;
    const fixed = ports.filter((port) => port.mode === "fixed-position");
    for (const port of fixed) result[port.id] = { ...port.offset! };
    // Keep the measured attachment area, but assign its slots in the order
    // chosen against opposite incidences instead of freezing identity order.
    const slotted = ports.filter((port) => port.mode === "free-in-slots");
    const along = (point: Point) => horizontal(side) ? point.x : point.y;
    const slots = slotted.map((port) => port.offset!).sort((a, b) => along(a) - along(b));
    slotted.sort((a, b) => (order[a.id] ?? 0) - (order[b.id] ?? 0) || compareText(a.id, b.id))
      .forEach((port, index) => { result[port.id] = { ...slots[index]! }; });
    const movable = ports.filter((port) => port.mode !== "fixed-position" && port.mode !== "free-in-slots");
    if (!movable.length) continue;
    // Stable topological selection lets free-order preferences interleave with
    // an immutable fixed-order subsequence, without conflating their meanings.
    const constrained = movable.filter((p) => p.mode === "fixed-order").sort((a, b) => a.order! - b.order! || compareText(a.id, b.id));
    const pending = new Set(movable), sequence: PortSpec[] = [];
    while (pending.size) {
      const nextFixed = constrained.find((p) => pending.has(p));
      const eligible = [...pending].filter((p) => p.mode !== "fixed-order" || p === nextFixed);
      eligible.sort((a, b) => (order[a.id] ?? a.order ?? 0) - (order[b.id] ?? b.order ?? 0) || compareText(a.id, b.id));
      sequence.push(eligible[0]!); pending.delete(eligible[0]!);
    }
    const padding = Math.min(endPadding, extent / 2), low = padding, high = extent - padding;
    const occupied = [...fixed, ...slotted].map((p) => along(p.offset!)).sort((a, b) => a - b);
    // Choose equally separated available slots. Fixed glyphs split a side into
    // intervals; no adjustable attachment is moved onto a numbered dock.
    const intervals: [number, number][] = [];
    let left = low;
    for (const at of occupied) { const end = Math.min(high, at - separation); if (end >= left) intervals.push([left, end]); left = Math.max(left, at + separation); }
    if (left <= high) intervals.push([left, high]);
    const capacity = intervals.reduce((sum, [a, b]) => sum + Math.floor((b - a + 1e-7) / separation) + 1, 0);
    if (capacity < sequence.length) throw new GraphDiagnosticError([{ code: "port-capacity", message: `Measured ${side} side has ${capacity} distinct slots for ${sequence.length} attachments`, ids: [node.id] }]);
    let positions: number[];
    if (!occupied.length) {
      const span = Math.min(high - low, Math.max(0, sequence.length - 1) * separation);
      positions = sequence.map((_, index) => extent / 2 - span / 2 + index * separation);
    } else {
      const slots = intervals.flatMap(([a, b]) => Array.from({ length: Math.floor((b - a + 1e-7) / separation) + 1 }, (_, i) => a + i * separation));
      positions = sequence.map((_, i) => slots[Math.floor((i + 0.5) * slots.length / sequence.length)]!);
    }
    sequence.forEach((port, index) => {
      const at = positions[index]!;
      result[port.id] = side === "north" ? { x: at, y: 0 } : side === "south" ? { x: at, y: node.height }
        : side === "west" ? { x: 0, y: at } : { x: node.width, y: at };
    });
  }
  return Object.freeze(result);
}

export function placePorts(graph: MeasuredGraph, nodes: readonly PlacedNode[], offsets: PortOffsets): PlacedPort[] {
  const positions = new Map(nodes.map((node) => [node.id, node]));
  return graph.nodes.flatMap((node) => node.ports.map((port) => {
    const at = positions.get(node.id), offset = offsets[port.id];
    if (!at || !offset) throw new GraphDiagnosticError([{ code: "unplaced-port", message: "Every port needs a measured owner and finalized offset", ids: [port.id] }]);
    return { id: port.id, nodeId: node.id, x: at.x + offset.x, y: at.y + offset.y };
  }));
}

export function portNormal(side: PortSpec["side"]): Point {
  return side === "north" ? { x: 0, y: -1 } : side === "south" ? { x: 0, y: 1 }
    : side === "east" ? { x: 1, y: 0 } : { x: -1, y: 0 };
}

export function centeredPortOffset(node: MeasuredNode, id: string | undefined, offsets: PortOffsets): number {
  return id ? offsets[id]!.x - node.width / 2 : 0;
}
