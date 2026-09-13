import type { DisplayGraph } from "../../../src/sitegen/graph-project.js";

/** Display-contract fixture: catalog ordinals are deliberately sparse and
 * large, independently of how many entries this measured fixture contains. */
export function dockInkFixture(): DisplayGraph {
  return {
    kind: "proofs", mapping: [],
    nodes: [
      { id: "c:Claims", semanticId: "Claims", kind: "concept", status: "open", ext: false,
        label: "A complete claim label long enough to wrap over several measured lines with χ and K₃", href: "claims.html",
        docks: [
          { id: "dock:Claims.first", statementId: "Claims.first", ordinal: 1, status: "open", href: "claims.html#first" },
          { id: "dock:Claims.last", statementId: "Claims.last", ordinal: 9876543210, status: "open", href: "claims.html#last" },
        ], ports: [
          { id: "first:out", nodeId: "c:Claims", semanticEndpointId: "Claims.first", side: "north", mode: "free-on-side" },
          { id: "last:out", nodeId: "c:Claims", semanticEndpointId: "Claims.last", side: "north", mode: "free-on-side" },
        ] },
      { id: "p:Proof", semanticId: "Proof", kind: "proof", status: "open", ext: false, label: "⊢", docks: [], ports: [
        { id: "first:in", nodeId: "p:Proof", semanticEndpointId: "Proof", side: "south", mode: "free-on-side" },
        { id: "last:in", nodeId: "p:Proof", semanticEndpointId: "Proof", side: "south", mode: "free-on-side" },
        { id: "proof:out", nodeId: "p:Proof", semanticEndpointId: "Proof", side: "north", mode: "free-on-side" },
      ] },
      { id: "s:Conclusion", semanticId: "Conclusion", kind: "statement", status: "open", ext: false, label: "Conclusion", docks: [], ports: [
        { id: "conclusion:in", nodeId: "s:Conclusion", semanticEndpointId: "Conclusion", side: "south", mode: "free-on-side" },
      ] },
    ], edges: [
      { id: "first", sourcePortId: "first:out", targetPortId: "first:in", kind: "assumption", minRankSpan: 1 },
      { id: "last", sourcePortId: "last:out", targetPortId: "last:in", kind: "assumption", minRankSpan: 1 },
      { id: "conclusion", sourcePortId: "proof:out", targetPortId: "conclusion:in", kind: "conclusion", minRankSpan: 1 },
    ],
  };
}
