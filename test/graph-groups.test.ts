import { describe, expect, it } from "vitest";
import { layoutGroups } from "../src/graph-layout/groups.js";
import { layoutGraph, translateGeometry } from "../src/graph-layout/index.js";
import { canonicalJson, normalizeGraph } from "../src/graph-layout/normalize.js";
import { layoutDag } from "../src/graph-layout/portfolio.js";
import { DEFAULT_PROFILE, GraphDiagnosticError, type GraphGeometry, type MeasuredGraph, type MeasuredNode, type PortSpec } from "../src/graph-layout/types.js";
import { validateGeometry } from "../src/graph-layout/validate.js";

type Incidence = { source: string; target: string; sourceSide?: PortSpec["side"]; targetSide?: PortSpec["side"] };
function fixture(ids: readonly string[], incidences: readonly Incidence[]): MeasuredGraph {
  const ports = new Map(ids.map((id) => [id, [] as PortSpec[]]));
  incidences.forEach((edge, i) => {
    for (const [nodeId, suffix, side] of [[edge.source, "source", edge.sourceSide ?? "north"], [edge.target, "target", edge.targetSide ?? "south"]] as const)
      ports.get(nodeId)!.push({ id: `edge-${i}:${suffix}`, nodeId, side, mode: "fixed-position", semanticEndpointId: `${nodeId}:statement-${i + 1}` });
  });
  const nodes: MeasuredNode[] = ids.map((id) => {
    const nodePorts = ports.get(id)!, width = 64 + nodePorts.length * 12, height = 48 + nodePorts.length * 12;
    return { id, kind: id.startsWith("proof") ? "proof" : "concept", width, height,
      labelBoxes: [{ x: 20, y: 20, width: width - 40, height: 12 }],
      ports: nodePorts.map((p) => {
        const peers = nodePorts.filter((q) => q.side === p.side), ordinal = peers.indexOf(p), horizontal = p.side === "north" || p.side === "south";
        const value = 16 + ordinal * 12;
        return { ...p, offset: horizontal ? { x: value, y: p.side === "north" ? 0 : height } : { x: p.side === "west" ? 0 : width, y: value } };
      }) };
  });
  return normalizeGraph({ nodes, edges: incidences.map((_, i) => ({ id: `edge-${i}`, sourcePortId: `edge-${i}:source`, targetPortId: `edge-${i}:target`, kind: "proof-incidence", minRankSpan: 1, semanticIds: [`semantic-edge-${i}`] })) });
}
const dag = (graph: MeasuredGraph): GraphGeometry => layoutDag(graph, { inputDigest: "outer", profile: { ...DEFAULT_PROFILE, cornerRadius: 0 } }).geometry;
const draw = (graph: MeasuredGraph): GraphGeometry => layoutGroups(graph, dag, "complete", { ...DEFAULT_PROFILE, cornerRadius: 0 });
function follow(geometry: GraphGeometry, id: string) {
  const sections = geometry.edges.find((e) => e.id === id)!.sections, byId = new Map(sections.map((s) => [s.id, s]));
  const referenced = new Set(sections.flatMap((s) => [...s.nextSectionIds]));
  let current = sections.find((s) => !referenced.has(s.id)); const result = [];
  while (current) { result.push(current); current = current.nextSectionIds[0] ? byId.get(current.nextSectionIds[0]) : undefined; }
  return result;
}

describe("expanded display SCCs with explicit semantic incidence gates", () => {
  it("keeps every internal member and externally connected incidence visible", () => {
    const graph = fixture(["a", "b", "premise", "result"], [
      { source: "a", target: "b" }, { source: "b", target: "a" }, { source: "premise", target: "a" }, { source: "b", target: "result" },
    ]), geometry = draw(graph), checked = validateGeometry(graph, geometry);
    expect(checked.valid, JSON.stringify(checked.diagnostics)).toBe(true);
    expect(geometry.nodes.map((n) => n.id)).toEqual(graph.nodes.map((n) => n.id));
    expect(geometry.ports.map((p) => p.id)).toEqual(graph.nodes.flatMap((n) => n.ports.map((p) => p.id)).sort());
    expect(geometry.edges.map((e) => e.id)).toEqual(graph.edges.map((e) => e.id));
    expect(geometry.groups).toHaveLength(1); expect(geometry.groups![0]!.memberIds).toEqual(["a", "b"]);
    expect(geometry.groups![0]!.gates).toHaveLength(2);
    expect(geometry.nodes.some((node) => node.id === geometry.groups![0]!.id)).toBe(false);
    for (const edge of graph.edges) {
      const sections = follow(geometry, edge.id);
      expect(sections.at(-1)!.terminalTargetPortId).toBe(edge.targetPortId);
      expect(sections.slice(0, -1).every((section) => !section.terminalTargetPortId)).toBe(true);
      const start = geometry.ports.find((p) => p.id === edge.sourcePortId)!;
      expect(sections[0]!.points[0]).toEqual({ x: start.x, y: start.y });
    }
    expect(follow(geometry, "edge-0").map((s) => s.role)).toEqual(["feedback"]);
    expect(follow(geometry, "edge-2").at(-1)!.role).toBe("group-adapter");
    expect(follow(geometry, "edge-3")[0]!.role).toBe("group-adapter");
  });
  it("joins two expanded groups through exactly identified boundary gates", () => {
    const graph = fixture(["a", "b", "c", "d"], [
      { source: "a", target: "b" }, { source: "b", target: "a" }, { source: "c", target: "d" }, { source: "d", target: "c" }, { source: "b", target: "c" },
    ]), geometry = draw(graph), chain = follow(geometry, "edge-4");
    expect(validateGeometry(graph, geometry).valid).toBe(true);
    expect(geometry.groups).toHaveLength(2);
    const gates = geometry.groups!.flatMap((g) => g.gates!);
    expect(gates).toHaveLength(2); expect(new Set(gates.map((g) => g.id)).size).toBe(2);
    expect(chain[0]!.role).toBe("group-adapter"); expect(chain.at(-1)!.role).toBe("group-adapter");
    for (const gate of gates) expect(chain.some((s) => s.points[0]!.x === gate.point.x && s.points[0]!.y === gate.point.y)
      && chain.some((s) => s.points.at(-1)!.x === gate.point.x && s.points.at(-1)!.y === gate.point.y)).toBe(true);
  });
  it("preserves actual self-loops and alternative proof incidence nodes", () => {
    const self = fixture(["self"], [{ source: "self", target: "self" }]), loop = draw(self);
    expect(validateGeometry(self, loop).valid).toBe(true); expect(loop.groups).toHaveLength(1);
    expect(loop.groups![0]!.gates).toEqual([]); expect(loop.edges[0]!.sections[0]!.role).toBe("feedback");
    const graph = fixture(["concept-a", "concept-b", "proof-1", "proof-2"], [
      { source: "concept-a", target: "proof-1" }, { source: "proof-1", target: "concept-b" },
      { source: "concept-b", target: "proof-2" }, { source: "proof-2", target: "concept-a" },
    ]), geometry = draw(graph);
    // This is a cycle in the grouping of display boxes. No circular-proof or
    // kernel-failure interpretation is introduced by geometry serialization.
    expect(validateGeometry(graph, geometry).valid).toBe(true);
    expect(geometry.groups![0]!.memberIds).toHaveLength(4);
    expect(geometry.nodes.filter((n) => n.id.startsWith("proof"))).toHaveLength(2);
    expect(geometry.edges).toHaveLength(4);
  });
  it("keeps numbered fixed ports, true arrows and east/west access clearances", () => {
    const graph = fixture(["a", "b", "external"], [
      { source: "a", target: "b", sourceSide: "east", targetSide: "west" },
      { source: "b", target: "a", sourceSide: "south", targetSide: "north" },
      { source: "a", target: "external", sourceSide: "west" },
    ]), geometry = draw(graph);
    expect(validateGeometry(graph, geometry).valid).toBe(true);
    for (const node of graph.nodes) for (const port of node.ports) {
      const at = geometry.nodes.find((n) => n.id === node.id)!, placed = geometry.ports.find((p) => p.id === port.id)!;
      expect(placed.x).toBeCloseTo(at.x + port.offset!.x); expect(placed.y).toBeCloseTo(at.y + port.offset!.y);
      expect(port.semanticEndpointId).toMatch(/statement-/);
    }
  });
  it("remains deterministic through input reorderings, quantization and packing translations", () => {
    const graph = fixture(["a", "b", "result"], [{ source: "a", target: "b" }, { source: "b", target: "a" }, { source: "a", target: "result" }]);
    const first = draw(graph), second = draw(normalizeGraph({ nodes: [...graph.nodes].reverse(), edges: [...graph.edges].reverse() }));
    expect(canonicalJson(first)).toBe(canonicalJson(second));
    const shifted = translateGeometry(first, 29, -13);
    expect(validateGeometry(graph, shifted).metrics).toEqual(validateGeometry(graph, first).metrics);
    expect(validateGeometry(graph, shifted).valid).toBe(true);
    const complete = layoutGraph(graph, { inputDigest: "packed", profile: { ...DEFAULT_PROFILE, cornerRadius: 0 } });
    expect(validateGeometry(graph, complete.geometry).valid).toBe(true);
  });
  it("diagnoses failed layouts under a fixed complete-envelope retry budget", () => {
    const graph = fixture(["a", "b"], [{ source: "a", target: "b" }, { source: "b", target: "a" }]);
    let calls = 0;
    expect(() => layoutGroups(graph, () => { calls++; throw new GraphDiagnosticError([{ code: "fixture-failure", message: "No valid outer candidate" }]); }, "failed")).toThrow(/scc-layout-invalid/);
    expect(calls).toBe(3);
  });
  it("joins callback routes by section topology even when their arrays are reversed", () => {
    const graph = fixture(["a", "b", "result"], [{ source: "a", target: "b" }, { source: "b", target: "a" }, { source: "a", target: "result" }]);
    const unordered = (outer: MeasuredGraph): GraphGeometry => {
      const geometry = dag(outer);
      return { ...geometry, edges: geometry.edges.map((edge) => {
        const section = follow(geometry, edge.id)[0]!, a = section.points[0]!, b = section.points[1]!, midpoint = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
        const first = { ...section, id: section.id + ":first", points: [a, midpoint], commands: undefined, nextSectionIds: [section.id + ":rest"], terminalTargetPortId: undefined };
        const rest = { ...section, id: section.id + ":rest", points: [midpoint, ...section.points.slice(1)], commands: undefined };
        return { ...edge, sections: [first, rest, ...edge.sections.filter((other) => other !== section)].reverse() };
      }) };
    };
    const geometry = layoutGroups(graph, unordered, "unordered", { ...DEFAULT_PROFILE, cornerRadius: 0 });
    expect(validateGeometry(graph, geometry).valid).toBe(true);
    expect(follow(geometry, "edge-2").at(-1)!.terminalTargetPortId).toBe("edge-2:target");
  });
  it("retains dense internal and parallel external incidences under lane pressure", () => {
    let state = 72315;
    const random = () => { state = Math.imul(state, 1664525) + 1013904223 | 0; return (state >>> 0) / 4294967296; };
    for (let sample = 0; sample < 24; sample++) {
      const n = 2 + sample % 5, members = Array.from({ length: n }, (_, i) => `member-${i}`), incidences: Incidence[] = [];
      members.forEach((source, i) => incidences.push({ source, target: members[(i + 1) % n]! }));
      for (const source of members) for (const target of members) if (source !== target && random() < 0.3) incidences.push({ source, target });
      incidences.push({ source: "premise", target: members[0]! }, { source: "premise", target: members[0]! },
        { source: members.at(-1)!, target: "result" }, { source: members[0]!, target: "result" });
      const graph = fixture([...members, "premise", "result"], incidences), geometry = draw(graph), result = validateGeometry(graph, geometry);
      expect(result.valid, `SCC pressure sample ${sample}: ${JSON.stringify(result.diagnostics)}`).toBe(true);
      expect(geometry.edges).toHaveLength(incidences.length);
      expect(geometry.groups![0]!.gates).toHaveLength(4);
      expect(result.metrics.overlaps).toBe(0);
    }
  });
});
