import { coordinateExtent, assertSeparation } from "./coordinates-bk.js";
import { placePorts, portNormal, portOffsets, type PortOffsets } from "./ports.js";
import { simplifyCollinear, quantizeGeometry, quantizePoint } from "./geometry.js";
import type { PortOrder, ProperGraph } from "./proper-graph.js";
import { DEFAULT_PROFILE, ENGINE_VERSION, GEOMETRY_SCHEMA_VERSION, GraphDiagnosticError, type GraphGeometry, type LayoutProfile, type PlacedNode, type PlacedPort, type Point, type Rect, type RouteSection } from "./types.js";

export type RankEnvelope = Readonly<{ rank: number; top: number; bottom: number; center: number }>;
export type RankBand = Readonly<{ rank: number; top: number; bottom: number; channels: number }>;
export type CorridorPlacement = Readonly<{
  nodes: readonly PlacedNode[]; ports: readonly PlacedPort[];
  rows: readonly RankEnvelope[]; bands: readonly RankBand[];
  x: readonly number[]; bounds: Rect; offsets: PortOffsets;
}>;

/** Whole row envelopes, with capacity-dependent inter-row bands. Dummies own
 * a positive-width slot throughout each traversed row. All diagonals stay in
 * the empty band; this is the reference geometry, never shortened by box tests. */
export function placeCorridors(graph: ProperGraph, layers: readonly (readonly number[])[], x: readonly number[], order: PortOrder = {}, profile: LayoutProfile = DEFAULT_PROFILE, options: {
  offsets?: PortOffsets; bandExpansion?: number;
} = {}): CorridorPlacement {
  assertSeparation(graph, layers, x, profile);
  const offsets = options.offsets ?? portOffsets(graph.source, order, profile.portSeparation);
  const terminal = Math.max(12, profile.clearance + 2);
  const heights = layers.map((layer) => layer.reduce((height, vertex) => Math.max(height, graph.vertices[vertex]!.height), 0));
  const rows: RankEnvelope[] = new Array(layers.length), bands: RankBand[] = new Array(Math.max(0, layers.length - 1));
  let y = profile.margin;
  for (let rank = layers.length - 1; rank >= 0; rank--) {
    const height = heights[rank]!;
    rows[rank] = { rank, top: y, bottom: y + height, center: y + height / 2 };
    y += height;
    if (rank) {
      // One horizontal channel per incidence is a safe capacity upper bound
      // for the orthogonal alternative. The polyline reuses these dimensions
      // so changes of route style never rely on compressed unreadable ranks.
      const channels = graph.segmentsByRank[rank - 1]!.length;
      const gap = Math.max(profile.rankGap, terminal * 2 + 8 + channels * profile.portSeparation) * (options.bandExpansion ?? 1);
      bands[rank - 1] = { rank: rank - 1, top: y + terminal, bottom: y + gap - terminal, channels };
      y += gap;
    }
  }
  const [left, right] = coordinateExtent(graph, x), translateX = profile.margin + terminal - left;
  const shifted = x.map((value) => value + translateX);
  const nodes = graph.source.nodes.map((node, i) => {
    const rank = graph.vertices[i]!.rank;
    return { id: node.id, rank, x: shifted[i]! - node.width / 2, y: rows[rank]!.center - node.height / 2, width: node.width, height: node.height };
  });
  return { nodes, ports: placePorts(graph.source, nodes, offsets), rows, bands, x: shifted, offsets,
    bounds: { x: 0, y: 0, width: graph.vertices.length ? right - left + 2 * (profile.margin + terminal) : 0, height: graph.vertices.length ? y + profile.margin : 0 } };
}

/** Standard north/south ports need no adapter. Other fixed directions escape
 * around their measured owner within the documented 24px neighbourhood. */
function terminalAdapter(node: PlacedNode, port: PlacedPort, side: "north" | "south" | "east" | "west", source: boolean, escape: number): Point[] {
  if ((source && side === "north") || (!source && side === "south")) return [{ x: port.x, y: port.y }];
  const normal = portNormal(side), end = { x: port.x + normal.x * escape, y: port.y + normal.y * escape };
  const east = side === "east" || (side !== "west" && port.x >= node.x + node.width / 2);
  const outsideX = east ? node.x + node.width + escape : node.x - escape;
  const channelY = source ? node.y - escape : node.y + node.height + escape;
  const points = simplifyCollinear([port, end, { x: outsideX, y: end.y }, { x: outsideX, y: channelY }].map(quantizePoint));
  return source ? points : [...points].reverse();
}

export function protectedEdgeSections(graph: ProperGraph, placement: CorridorPlacement, edgeIndex: number, profile: LayoutProfile = DEFAULT_PROFILE, placedPortIndex?: ReadonlyMap<string, PlacedPort>): RouteSection[] {
  const edge = graph.source.edges[edgeIndex]!, chain = graph.chains[edgeIndex]!;
  const ports = placedPortIndex ?? new Map(placement.ports.map((port) => [port.id, port]));
  const source = ports.get(edge.sourcePortId)!, target = ports.get(edge.targetPortId)!;
  const sourceNode = placement.nodes[chain[0]!]!, targetNode = placement.nodes[chain.at(-1)!]!;
  const sourceSpec = graph.source.nodes[chain[0]!]!.ports.find((p) => p.id === source.id)!;
  const targetSpec = graph.source.nodes[chain.at(-1)!]!.ports.find((p) => p.id === target.id)!;
  const escape = Math.max(12, profile.clearance + 2);
  if (escape > 24) throw new GraphDiagnosticError([{ code: "terminal-envelope", message: "This profile exceeds the documented terminal-adapter envelope", ids: [edge.id] }]);
  const startAdapter = terminalAdapter(sourceNode, source, sourceSpec.side, true, escape), endAdapter = terminalAdapter(targetNode, target, targetSpec.side, false, escape);
  const start = startAdapter.at(-1)!, end = endAdapter[0]!, points: Point[] = [start];
  for (let i = 0; i + 1 < chain.length; i++) {
    const u = chain[i]!, v = chain[i + 1]!, rank = graph.vertices[u]!.rank;
    const band = placement.bands[rank]!;
    const fromX = i === 0 ? start.x : placement.x[u]!, toX = i + 2 === chain.length ? end.x : placement.x[v]!;
    points.push({ x: fromX, y: band.bottom }, { x: toX, y: band.top });
  }
  points.push(end);
  const sections: { id: string; points: Point[]; role: RouteSection["role"] }[] = [];
  if (startAdapter.length > 1) sections.push({ id: `${edge.id}:source`, points: startAdapter, role: "terminal-adapter" });
  // Simplify the geometry that will actually be published. A pre-quantization
  // near-collinearity can straddle a half-grid boundary; deleting its terminal
  // stubs first would turn the rounded endpoints into a slanted direct edge.
  sections.push({ id: `${edge.id}:corridor`, points: simplifyCollinear(points.map(quantizePoint)), role: "rank-corridor" });
  if (endAdapter.length > 1) sections.push({ id: `${edge.id}:target`, points: endAdapter, role: "terminal-adapter" });
  return sections.map((section, i) => ({ ...section, nextSectionIds: i + 1 < sections.length ? [sections[i + 1]!.id] : [],
    ...(i + 1 === sections.length ? { terminalTargetPortId: target.id } : {}) }));
}

export function routeProtected(graph: ProperGraph, placement: CorridorPlacement, metadata: { inputDigest?: string; profileId?: string } = {}, profile: LayoutProfile = DEFAULT_PROFILE): GraphGeometry {
  const ports = new Map(placement.ports.map((port) => [port.id, port]));
  return quantizeGeometry({ schemaVersion: GEOMETRY_SCHEMA_VERSION, engineVersion: ENGINE_VERSION,
    profileId: metadata.profileId ?? profile.id, inputDigest: metadata.inputDigest ?? "",
    bounds: placement.bounds, nodes: placement.nodes, ports: placement.ports,
    edges: graph.source.edges.map((edge, edgeIndex) => ({ id: edge.id, sections: protectedEdgeSections(graph, placement, edgeIndex, profile, ports) })) });
}
