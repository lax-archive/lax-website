/** Pure layout contract. No DOM, filesystem, URLs, author text, or statuses. */
export type Id = string;
export type Point = Readonly<{ x: number; y: number }>;
export type Rect = Readonly<{ x: number; y: number; width: number; height: number }>;
export type PortSpec = Readonly<{
  id: Id; nodeId: Id; semanticEndpointId: Id;
  side: "north" | "south" | "east" | "west";
  mode: "free-on-side" | "fixed-order" | "fixed-position";
  order?: number;
  /** Node-local, measured from the TOP LEFT (not its center). */
  offset?: Point;
}>;
export type Footprint = Readonly<{
  /** An attachment area contains its owner's outgoing dock adapters, while
   * remaining an obstacle to all unrelated incidences. Labels/docks obstruct
   * independently, including within this area. */
  id: Id; kind: "body" | "dock" | "rail" | "label" | "attachment-area";
  bounds: Rect; semanticEndpointId?: Id;
}>;
export type MeasuredNode = Readonly<{
  id: Id; kind: "concept" | "statement" | "proof" | "submission" | "scc";
  width: number; height: number;
  labelBoxes: readonly Rect[];
  ports: readonly PortSpec[];
  /** Optional complete visible footprints; otherwise the whole box obstructs. */
  footprints?: readonly Footprint[];
}>;
export type LayoutEdge = Readonly<{
  id: Id; sourcePortId: Id; targetPortId: Id; kind: string;
  minRankSpan: number; weight?: number;
  /** Input incidences represented by this edge, never anonymous array offsets. */
  semanticIds?: readonly Id[];
}>;
export type MeasuredGraph = Readonly<{
  nodes: readonly MeasuredNode[]; edges: readonly LayoutEdge[];
}>;
export type PathCommand = Readonly<{ kind: "M" | "L"; p: Point }> |
  Readonly<{ kind: "Q"; control: Point; p: Point }>;
export type RouteSection = Readonly<{
  id: Id; points: readonly Point[]; nextSectionIds: readonly Id[];
  terminalTargetPortId?: Id;
  /** Only terminal/group adapters and edges internal to a verified SCC may
   * move backward. Default role is an ordinary upward rank corridor. */
  role?: "rank-corridor" | "terminal-adapter" | "group-adapter" | "feedback";
  /** Root SVG coordinates, checked independently from the reference polyline. */
  commands?: readonly PathCommand[];
}>;
export type PlacedNode = Rect & Readonly<{ id: Id; rank?: number; parentId?: Id }>;
export type PlacedPort = Point & Readonly<{ id: Id; nodeId: Id }>;
export type PlacedGroup = Rect & Readonly<{
  id: Id; memberIds: readonly Id[]; labelBoxes: readonly Rect[];
  /** One explicit boundary attachment for each external incidence. Gates are
   * layout-only objects, not additional semantic ports or mathematical nodes. */
  gates?: readonly Readonly<{ id: Id; edgeId: Id; side: PortSpec["side"]; point: Point }>[];
  /** A "sibling-proofs" group is a concept whose statements prove one another;
   * it is acyclic at statement level and is drawn without a cycle envelope. */
  kind?: "cycle" | "sibling-proofs";
}>;
export type GraphGeometry = Readonly<{
  schemaVersion: number; engineVersion: string; profileId: string; inputDigest: string;
  bounds: Rect;
  nodes: readonly PlacedNode[]; ports: readonly PlacedPort[];
  edges: readonly Readonly<{ id: Id; sections: readonly RouteSection[] }>[];
  groups?: readonly PlacedGroup[];
}>;
export type Diagnostic = Readonly<{
  code: string; message: string; ids?: readonly Id[];
}>;
export type GeometryMetrics = Readonly<{
  crossings: number; repeatedCrossingPairs: number; endpointTouches: number;
  tangencies: number; multiwayCrossings: number; overlaps: number;
  bends: number; length: number; width: number; height: number;
  minimumCrossingAngle: number | null;
}>;
export type ValidationResult = Readonly<{
  valid: boolean; diagnostics: readonly Diagnostic[]; metrics: GeometryMetrics;
}>;
export type LayoutProfile = Readonly<{
  id: string; nodeGap: number; dummyGap: number; rankGap: number;
  clearance: number; portSeparation: number; margin: number; cornerRadius: number;
  rankPivots: number; sweeps: number; siftingMoves: number;
  exactLayerLimit: number; dpStates: number; expandedVertices: number;
  routingExpansions: number; candidates: number;
}>;
export const ENGINE_VERSION = "lax-layout-1.2.0";
export const GEOMETRY_SCHEMA_VERSION = 1;
export const QUANTUM = 0.001;
/** Work budgets, not original-node cutoffs. Corpus evidence may version them. */
export const DEFAULT_PROFILE: LayoutProfile = Object.freeze({
  id: "readable-v3", nodeGap: 40, dummyGap: 16, rankGap: 32,
  clearance: 8, portSeparation: 16, margin: 24, cornerRadius: 4,
  rankPivots: 4096, sweeps: 8, siftingMoves: 4000,
  exactLayerLimit: 16, dpStates: 2_000_000, expandedVertices: 500_000,
  routingExpansions: 100_000, candidates: 12,
});

export class GraphDiagnosticError extends Error {
  constructor(readonly diagnostics: readonly Diagnostic[]) {
    super(diagnostics.map((d) => `${d.code}: ${d.message}${d.ids?.length ? ` [${d.ids.join(", ")}]` : ""}`).join("\n"));
    this.name = "GraphDiagnosticError";
  }
}
