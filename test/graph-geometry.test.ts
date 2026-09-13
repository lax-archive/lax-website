import { describe, expect, it } from "vitest";
import { canonicalJson, compareText, normalizeGraph } from "../src/graph-layout/normalize.js";
import { pathData, polylineCommands, quantize, quantizeGeometry, roundCorners, simplifyCollinear } from "../src/graph-layout/geometry.js";
import { commandBends, CURVE_DEVIATION, flattenCommands, parsePathData, routeMetrics, segmentHitsRect, segmentIntersection, validateGeometry } from "../src/graph-layout/validate.js";
import type { GraphGeometry, MeasuredGraph, MeasuredNode, Point } from "../src/graph-layout/types.js";

const node = (id: string, source: boolean): MeasuredNode => ({ id, kind: "concept", width: 40, height: 24,
  labelBoxes: [{ x: 8, y: 6, width: 24, height: 12 }], ports: [{ id: id + ":port", nodeId: id, semanticEndpointId: id,
    side: source ? "north" : "south", mode: "fixed-position", offset: { x: 20, y: source ? 0 : 24 } }] });
function fixture(): { graph: MeasuredGraph; geometry: GraphGeometry } {
  return { graph: normalizeGraph({ nodes: [node("u", true), node("v", false)], edges: [{ id: "e", sourcePortId: "u:port", targetPortId: "v:port", kind: "import", minRankSpan: 1 }] }),
    geometry: { schemaVersion: 1, engineVersion: "test", profileId: "test", inputDigest: "test", bounds: { x: 0, y: 0, width: 80, height: 120 },
      nodes: [{ id: "u", x: 20, y: 80, width: 40, height: 24, rank: 0 }, { id: "v", x: 20, y: 8, width: 40, height: 24, rank: 1 }],
      ports: [{ id: "u:port", nodeId: "u", x: 40, y: 80 }, { id: "v:port", nodeId: "v", x: 40, y: 32 }],
      edges: [{ id: "e", sections: [{ id: "e:route", points: [{ x: 40, y: 80 }, { x: 40, y: 32 }], nextSectionIds: [], terminalTargetPortId: "v:port" }] }] } };
}
const route = (id: string, points: Point[], sourcePort = id + ":a", targetPort = id + ":b") => ({ id, points, source: sourcePort, target: targetPort, sourcePort, targetPort });
const bounds = { x: -10, y: -10, width: 200, height: 200 };

/** Hand-specified geometry, independent of the layout/group implementations. */
function groupFixture(): { graph: MeasuredGraph; geometry: GraphGeometry } {
  const at = [
    { id: "a", x: 60, y: 70, width: 40, height: 20, rank: 0, parentId: "cycle" },
    { id: "b", x: 140, y: 70, width: 40, height: 20, rank: 0, parentId: "cycle" },
    { id: "c", x: 140, y: 0, width: 40, height: 20, rank: 1 },
  ];
  const ports = [
    { id: "a:n", nodeId: "a", x: 80, y: 70 }, { id: "a:s", nodeId: "a", x: 88, y: 90 },
    { id: "b:n", nodeId: "b", x: 168, y: 70 }, { id: "b:s", nodeId: "b", x: 152, y: 90 },
    { id: "b:external", nodeId: "b", x: 156, y: 70 }, { id: "c:s", nodeId: "c", x: 156, y: 20 },
  ];
  const edges = [{ id: "ab", sourcePortId: "a:n", targetPortId: "b:s", kind: "premise", minRankSpan: 1 },
    { id: "ba", sourcePortId: "b:n", targetPortId: "a:s", kind: "premise", minRankSpan: 1 },
    { id: "bc", sourcePortId: "b:external", targetPortId: "c:s", kind: "conclusion", minRankSpan: 1 }];
  const graph = normalizeGraph({ nodes: at.map((n) => ({ id: n.id, kind: "concept", width: n.width, height: n.height, labelBoxes: [],
    ports: ports.filter((p) => p.nodeId === n.id).map((p) => ({ id: p.id, nodeId: n.id, semanticEndpointId: n.id, side: p.y === n.y ? "north" : "south", mode: "fixed-position", offset: { x: p.x - n.x, y: p.y - n.y } })) })), edges } as MeasuredGraph);
  const geometry: GraphGeometry = { schemaVersion: 1, engineVersion: "test", profileId: "test", inputDigest: "test", bounds: { x: 0, y: 0, width: 260, height: 260 }, nodes: at, ports,
    groups: [{ id: "cycle", x: 40, y: 40, width: 180, height: 180, memberIds: ["a", "b"], labelBoxes: [], gates: [{ id: "cycle:bc", edgeId: "bc", side: "north", point: { x: 156, y: 40 } }] }],
    edges: [
      { id: "ab", sections: [{ id: "ab:route", role: "feedback", points: [{ x: 80, y: 70 }, { x: 80, y: 58 }, { x: 130, y: 58 }, { x: 130, y: 108 }, { x: 152, y: 108 }, { x: 152, y: 90 }], nextSectionIds: [], terminalTargetPortId: "b:s" }] },
      { id: "ba", sections: [{ id: "ba:route", role: "feedback", points: [{ x: 168, y: 70 }, { x: 168, y: 46 }, { x: 200, y: 46 }, { x: 200, y: 126 }, { x: 88, y: 126 }, { x: 88, y: 90 }], nextSectionIds: [], terminalTargetPortId: "a:s" }] },
      { id: "bc", sections: [{ id: "bc:inside", role: "group-adapter", points: [{ x: 156, y: 70 }, { x: 156, y: 40 }], nextSectionIds: ["bc:outside"] },
        { id: "bc:outside", role: "rank-corridor", points: [{ x: 156, y: 40 }, { x: 156, y: 20 }], nextSectionIds: [], terminalTargetPortId: "c:s" }] },
    ] };
  return { graph, geometry };
}

describe("immutable permission-free geometry contract", () => {
  it("resolves equivalent half-grid arithmetic consistently without merging distinct quantized positions", () => {
    expect(quantize(112.88049999999998)).toBe(112.881);
    expect(quantize(112.8805)).toBe(112.881);
    expect(quantize(-112.88050000000002)).toBe(-112.88);
    expect(quantize(-112.8805)).toBe(-112.88);
    expect(quantize(112.8805 - 1e-10)).toBe(112.88);
    expect(quantize(112.8805 + 1e-10)).toBe(112.881);
    for (const value of [-112.8805, -0.0005, 0, 0.0005, 112.8805])
      expect(quantize(quantize(value))).toBe(quantize(value));
  });

  it("allowlists fields, preserves identities and ignores input array order", () => {
    const { graph } = fixture();
    const decorated = { ...graph, privateView: "secret", nodes: graph.nodes.map((n) => ({ ...n, title: "private title", source: "private repo" })), edges: [...graph.edges].reverse() };
    const clean = normalizeGraph(decorated);
    expect(canonicalJson(clean)).toBe(canonicalJson(graph));
    expect(canonicalJson(normalizeGraph({ nodes: [...graph.nodes].reverse(), edges: graph.edges }))).toBe(canonicalJson(graph));
    expect(Object.isFrozen(clean.nodes[0]!.ports[0])).toBe(true);
    expect(["𐀀", "\uE000", "a"].sort(compareText)).toEqual(["a", "\uE000", "𐀀"]);
  });
  it("diagnoses missing incidences, duplicate identities and impossible ports", () => {
    const { graph } = fixture();
    expect(() => normalizeGraph({ ...graph, nodes: [graph.nodes[0]!] })).toThrow(/missing-endpoint/);
    expect(() => normalizeGraph({ ...graph, edges: [...graph.edges, ...graph.edges] })).toThrow(/duplicate-edge/);
    expect(() => normalizeGraph({ ...graph, nodes: [{ ...graph.nodes[0]!, width: 1 }, graph.nodes[1]!] })).toThrow(/footprint-outside|fixed-position/);
    expect(() => normalizeGraph({ ...graph, edges: [{ ...graph.edges[0]!, minRankSpan: 0 }] })).toThrow(/minimum-span/);
  });
});

describe("independent final-geometry validator", () => {
  it("accepts a straight upward path and its serialized, quantized geometry", () => {
    const { graph, geometry } = fixture();
    const final = quantizeGeometry({ ...geometry, edges: geometry.edges.map((edge) => ({ ...edge,
      sections: edge.sections.map((section) => ({ ...section, commands: parsePathData(pathData(polylineCommands(section.points))) })) })) });
    expect(validateGeometry(graph, final)).toMatchObject({ valid: true, metrics: { crossings: 0, overlaps: 0, bends: 0, length: 48 } });
  });
  it("detects data loss, fixed dock changes, broken sections and nonfinite cache bytes", () => {
    const { graph, geometry } = fixture();
    expect(validateGeometry(graph, { ...geometry, edges: [] }).diagnostics.map((d) => d.code)).toContain("edge-roundtrip");
    expect(validateGeometry(graph, { ...geometry, ports: geometry.ports.map((p) => ({ ...p, x: p.x + 1 })) }).diagnostics.map((d) => d.code)).toContain("fixed-port");
    expect(validateGeometry(graph, { ...geometry, nodes: geometry.nodes.map((n) => ({ ...n, x: Infinity })) }).valid).toBe(false);
    expect(validateGeometry(graph, { ...geometry, edges: [{ id: "e", sections: [{ ...geometry.edges[0]!.sections[0]!, nextSectionIds: ["absent"] }] }] }).diagnostics.map((d) => d.code)).toContain("missing-section");
  });
  it("rejects false feedback and backward ordinary routes", () => {
    const { graph, geometry } = fixture();
    const section = geometry.edges[0]!.sections[0]!;
    const points = [section.points[0]!, { x: 40, y: 90 }, section.points[1]!];
    expect(validateGeometry(graph, { ...geometry, edges: [{ id: "e", sections: [{ ...section, points }] }] }).diagnostics.map((d) => d.code)).toContain("reverse-flow");
    expect(validateGeometry(graph, { ...geometry, edges: [{ id: "e", sections: [{ ...section, role: "feedback", points }] }] }).diagnostics.map((d) => d.code)).toContain("feedback-outside-scc");
  });
  it("finds nonincident obstacles including label ink and arrowhead regions", () => {
    const { graph, geometry } = fixture();
    const extra: MeasuredNode = { id: "obstacle", kind: "concept", width: 10, height: 10, labelBoxes: [], ports: [] };
    const result = validateGeometry({ ...graph, nodes: [...graph.nodes, extra] }, { ...geometry,
      nodes: [...geometry.nodes, { ...extra, x: 35, y: 50 }] });
    expect(result.diagnostics.map((d) => d.code)).toContain("obstacle-collision");
  });
  it("is translation invariant, including negative intermediate positions", () => {
    const { graph, geometry } = fixture();
    const move = (p: Point) => ({ ...p, x: p.x - 500, y: p.y + 23 });
    const translated: GraphGeometry = { ...geometry, bounds: { ...geometry.bounds, ...move(geometry.bounds) },
      nodes: geometry.nodes.map((n) => ({ ...n, ...move(n) })), ports: geometry.ports.map((p) => ({ ...p, ...move(p) })),
      edges: geometry.edges.map((e) => ({ ...e, sections: e.sections.map((s) => ({ ...s, points: s.points.map(move) })) })) };
    expect(validateGeometry(graph, translated)).toEqual(validateGeometry(graph, geometry));
  });
  it("checks source/target normals, minimum approach and emitted rank feasibility", () => {
    const { graph, geometry } = fixture(), section = geometry.edges[0]!.sections[0]!;
    const edit = (points: Point[]) => ({ ...geometry, edges: [{ id: "e", sections: [{ ...section, points }] }] });
    expect(validateGeometry(graph, edit([{ x: 40, y: 80 }, { x: 45, y: 68 }, { x: 40, y: 44 }, { x: 40, y: 32 }])).diagnostics.map((d) => d.code)).toContain("source-direction");
    expect(validateGeometry(graph, edit([{ x: 40, y: 80 }, { x: 40, y: 50 }, { x: 45, y: 42 }, { x: 40, y: 32 }])).diagnostics.map((d) => d.code)).toContain("terminal-direction");
    expect(validateGeometry(graph, edit([{ x: 40, y: 80 }, { x: 40, y: 45 }, { x: 45, y: 35 }, { x: 40, y: 35 }, { x: 40, y: 32 }])).diagnostics.map((d) => d.code)).toContain("terminal-direction");
    expect(validateGeometry({ ...graph, edges: [{ ...graph.edges[0]!, minRankSpan: 2 }] }, geometry).diagnostics.map((d) => d.code)).toContain("rank-feasibility");
    expect(validateGeometry(graph, { ...geometry, nodes: geometry.nodes.map((n) => ({ ...n, rank: 0.5 })) }).diagnostics.map((d) => d.code)).toContain("invalid-rank");
  });
  it("checks the complete reference route even when emitted commands look safe", () => {
    const { graph, geometry } = fixture(), original = geometry.edges[0]!.sections[0]!;
    const bad = [{ x: 40, y: 80 }, { x: 40, y: 90 }, { x: 40, y: 32 }];
    const reference = { ...geometry, edges: [{ id: "e", sections: [{ ...original, points: bad, commands: polylineCommands(original.points) }] }] };
    expect(validateGeometry(graph, reference).diagnostics.map((d) => d.code)).toContain("reverse-flow");
    const rendered = { ...geometry, edges: [{ id: "e", sections: [{ ...original, commands: polylineCommands(bad) }] }] };
    expect(validateGeometry(graph, rendered).diagnostics.map((d) => d.code)).toContain("reverse-flow");
  });
  it("rejects self retracing independently of intersections between edge pairs", () => {
    const { graph, geometry } = fixture(), section = geometry.edges[0]!.sections[0]!;
    const points = [{ x: 40, y: 80 }, { x: 40, y: 60 }, { x: 60, y: 60 }, { x: 45, y: 60 }, { x: 45, y: 44 }, { x: 40, y: 44 }, { x: 40, y: 32 }];
    const result = validateGeometry(graph, { ...geometry, edges: [{ id: "e", sections: [{ ...section, points }] }] });
    expect(result.diagnostics.map((d) => d.code)).toContain("route-self-intersection");
    expect(result.metrics.overlaps).toBe(0);
  });
  it("checks arrowhead exclusion regions against nearby label ink", () => {
    const { graph, geometry } = fixture();
    const nearby: MeasuredNode = { id: "nearby", kind: "concept", width: 1, height: 1, ports: [], footprints: [], labelBoxes: [{ x: 0, y: 0, width: 1, height: 1 }] };
    const result = validateGeometry({ ...graph, nodes: [...graph.nodes, nearby] }, { ...geometry,
      nodes: [...geometry.nodes, { id: "nearby", x: 42, y: 35, width: 1, height: 1 }] });
    expect(result.diagnostics.map((d) => d.code)).toContain("arrowhead-obstacle");
    expect(result.diagnostics.map((d) => d.code)).not.toContain("obstacle-collision");
  });
  it("rejects touching arrowhead regions even when the centerlines stay apart", () => {
    const { graph, geometry } = fixture();
    const nodes = graph.nodes.map((n) => ({ ...n, ports: [...n.ports, { ...n.ports[0]!, id: n.id + ":second", offset: { ...n.ports[0]!.offset!, x: 24 } }] }));
    const extra = { ...graph.edges[0]!, id: "second", sourcePortId: "u:second", targetPortId: "v:second" };
    const result = validateGeometry({ nodes, edges: [...graph.edges, extra] }, { ...geometry,
      ports: [...geometry.ports, ...geometry.ports.map((p) => ({ ...p, id: p.nodeId + ":second", x: p.x + 4 }))],
      edges: [...geometry.edges, { id: "second", sections: [{ id: "second:route", points: [{ x: 44, y: 80 }, { x: 44, y: 32 }], nextSectionIds: [], terminalTargetPortId: "v:second" }] }] });
    expect(result.diagnostics.map((d) => d.code)).toContain("arrowhead-overlap");
    expect(result.diagnostics.map((d) => d.code)).not.toContain("arrowhead-collision");
  });
  it("rejects extra identities and malformed cache objects without throwing", () => {
    const { graph, geometry } = fixture();
    expect(validateGeometry(graph, { ...geometry, nodes: [...geometry.nodes, { ...geometry.nodes[0]!, id: "extra", x: 0, y: 0 }] }).diagnostics.map((d) => d.code)).toContain("node-roundtrip");
    expect(validateGeometry(graph, { ...geometry, edges: [null] } as unknown as GraphGeometry).diagnostics.map((d) => d.code)).toContain("geometry-schema");
    const section = geometry.edges[0]!.sections[0]!;
    expect(validateGeometry(graph, { ...geometry, edges: [{ id: "e", sections: [{ ...section, role: "anything" } as never] }] }).diagnostics.map((d) => d.code)).toContain("route-role");
  });
});

describe("intersection and curve oracles", () => {
  it("counts rounded corners once rather than every flattening segment", () => {
    const commands = parsePathData("M0,40 L0,20 Q0,10 10,10 L20,10 Q30,10 30,0 L30,-10");
    expect(flattenCommands(commands).length).toBeGreaterThan(10);
    expect(commandBends(commands)).toBe(2);
    expect(commandBends(parsePathData("M0,0 L10,0 L20,0"))).toBe(0);
  });
  it("checks exact quadratic derivatives and terminal runs below flattening tolerance", () => {
    const { graph, geometry } = fixture(), section = geometry.edges[0]!.sections[0]!;
    const curve = (path: string): GraphGeometry => ({ ...geometry, edges: [{ id: "e", sections: [{ ...section, commands: parsePathData(path) }] }] });
    // This subpixel backward derivative is smaller than the flattening error
    // bound; a flattened chord alone would report perfectly upward flow.
    const reversing = curve("M40,80 L40,60 Q40,60.001 40,40 L40,32");
    expect(validateGeometry(graph, reversing).diagnostics.map((d) => d.code)).toContain("reverse-flow");
    // An almost vertical quadratic remains curved right up to the target;
    // flattening it into a line must not invent a safe arrowhead approach.
    const terminal = curve("M40,80 L40,44 Q40.001,38 40,32");
    expect(validateGeometry(graph, terminal).diagnostics.map((d) => d.code)).toContain("terminal-direction");
  });
  it("distinguishes proper crossings, positive runs, shared endpoints and tangencies", () => {
    expect(segmentIntersection({ x: 0, y: 0 }, { x: 10, y: 10 }, { x: 0, y: 10 }, { x: 10, y: 0 })).toEqual({ kind: "point", p: { x: 5, y: 5 } });
    expect(segmentIntersection({ x: 0, y: 0 }, { x: 10, y: 0 }, { x: 2, y: 0 }, { x: 8, y: 0 })?.kind).toBe("overlap");
    expect(routeMetrics([route("a", [{ x: 0, y: 0 }, { x: 10, y: 10 }]), route("b", [{ x: 0, y: 10 }, { x: 10, y: 0 }])], bounds)).toMatchObject({ crossings: 1, tangencies: 0 });
    expect(routeMetrics([route("a", [{ x: 0, y: 0 }, { x: 10, y: 0 }], "shared"), route("b", [{ x: 0, y: 0 }, { x: 10, y: 10 }], "shared")], bounds)).toMatchObject({ crossings: 0, endpointTouches: 0 });
    expect(routeMetrics([route("a", [{ x: 0, y: 0 }, { x: 10, y: 0 }]), route("b", [{ x: 0, y: 5 }, { x: 5, y: 0 }, { x: 10, y: 5 }])], bounds)).toMatchObject({ crossings: 0, tangencies: 1 });
  });
  it("does not exempt incident edge pairs that cross again away from their endpoint", () => {
    const a = route("a", [{ x: 0, y: 0 }, { x: 20, y: 20 }], "common");
    const b = route("b", [{ x: 0, y: 0 }, { x: 0, y: 20 }, { x: 20, y: 0 }], "common");
    expect(routeMetrics([a, b], bounds).crossings).toBe(1);
  });
  it("deduplicates a crossing at a polyline vertex and reports multiway sites", () => {
    const a = route("a", [{ x: 0, y: 0 }, { x: 5, y: 5 }, { x: 10, y: 10 }]);
    const b = route("b", [{ x: 0, y: 10 }, { x: 5, y: 5 }, { x: 10, y: 0 }]);
    expect(routeMetrics([a, b], bounds).crossings).toBe(1);
    const c = route("c", [{ x: 0, y: 5 }, { x: 10, y: 5 }]);
    expect(routeMetrics([a, b, c], bounds)).toMatchObject({ crossings: 3, multiwayCrossings: 1 });
  });
  it("captures the old node-clear shortcut defect without changing any edge", () => {
    const other = route("b", [{ x: 20, y: 90 }, { x: 20, y: 30 }]);
    const safe = route("a", [{ x: 0, y: 100 }, { x: 0, y: 20 }, { x: 40, y: 20 }, { x: 40, y: 0 }]);
    const shortcut = route("a", [safe.points[0]!, safe.points.at(-1)!]);
    expect(routeMetrics([safe, other], bounds).crossings).toBe(0);
    expect(routeMetrics([shortcut, other], bounds).crossings).toBe(1);
  });
  it("detects a rounding collision missed by the original polyline", () => {
    const points = [{ x: 0, y: 20 }, { x: 0, y: 0 }, { x: 20, y: 0 }];
    const obstacle = { x: 0.9, y: 0.9, width: 0.2, height: 0.2 };
    expect(points.slice(1).some((p, i) => segmentHitsRect(points[i]!, p, obstacle))).toBe(false);
    const commands = parsePathData(pathData(roundCorners(points, 4)));
    const flat = flattenCommands(commands);
    expect(flat.slice(1).some((p, i) => segmentHitsRect(flat[i]!, p, { x: obstacle.x - CURVE_DEVIATION, y: obstacle.y - CURVE_DEVIATION, width: obstacle.width + 2 * CURVE_DEVIATION, height: obstacle.height + 2 * CURVE_DEVIATION }))).toBe(true);
  });
  it("keeps reversals and handles degenerate rectangles and tiny segments", () => {
    expect(simplifyCollinear([{ x: 0, y: 0 }, { x: 10, y: 0 }, { x: 2, y: 0 }])).toHaveLength(3);
    expect(segmentHitsRect({ x: -1, y: 0 }, { x: 1, y: 0 }, { x: 0, y: 0, width: 0, height: 0 })).toBe(true);
    expect(segmentIntersection({ x: 0, y: 0 }, { x: 0.001, y: 0 }, { x: 0.0005, y: -1 }, { x: 0.0005, y: 1 })?.kind).toBe("point");
  });
});

describe("independent group boundary and section validation", () => {
  it("accepts true internal directions, containing envelopes and joined exterior gates", () => {
    const { graph, geometry } = groupFixture(), checked = validateGeometry(graph, geometry);
    expect(checked.diagnostics).toEqual([]);
    expect(checked.valid).toBe(true);
  });
  it("rejects missing, displaced, duplicated and misattributed gates", () => {
    const { graph, geometry } = groupFixture(), group = geometry.groups![0]!, gate = group.gates![0]!;
    const missing = { ...geometry, groups: [{ ...group, gates: [] }] };
    expect(validateGeometry(graph, missing).diagnostics.map((d) => d.code)).toContain("missing-gate");
    const displaced = { ...geometry, groups: [{ ...group, gates: [{ ...gate, point: { x: 160, y: 40 } }] }] };
    expect(validateGeometry(graph, displaced).diagnostics.map((d) => d.code)).toContain("wrong-gate");
    const wrongSide = { ...geometry, groups: [{ ...group, gates: [{ ...gate, side: "south" as const }] }] };
    expect(validateGeometry(graph, wrongSide).diagnostics.map((d) => d.code)).toContain("gate-boundary");
    const duplicate = { ...geometry, groups: [{ ...group, gates: [gate, gate] }] };
    expect(validateGeometry(graph, duplicate).diagnostics.map((d) => d.code)).toContain("gate-identity");
    const internal = { ...geometry, groups: [{ ...group, gates: [{ ...gate, edgeId: "ab" }] }] };
    expect(validateGeometry(graph, internal).diagnostics.map((d) => d.code)).toContain("gate-incidence");
  });
  it("requires an explicit gate join and reserves the marker for the actual conclusion", () => {
    const { graph, geometry } = groupFixture(), edge = geometry.edges.find((e) => e.id === "bc")!;
    const joined = { ...geometry, edges: geometry.edges.map((e) => e.id !== "bc" ? e : { id: "bc", sections: [{ id: "bc:joined", role: "rank-corridor" as const,
      points: [edge.sections[0]!.points[0]!, edge.sections[1]!.points.at(-1)!], nextSectionIds: [], terminalTargetPortId: "c:s" }] }) };
    expect(validateGeometry(graph, joined).diagnostics.map((d) => d.code)).toContain("gate-section-join");
    const marker = { ...geometry, edges: geometry.edges.map((e) => e.id !== "bc" ? e : { ...e, sections: e.sections.map((s, i) => i ? s : { ...s, terminalTargetPortId: "c:s" }) }) };
    expect(validateGeometry(graph, marker).diagnostics.map((d) => d.code)).toContain("boundary-marker");
  });
  it("does not let feedback escape its group or treat an arbitrary group as an SCC", () => {
    const { graph, geometry } = groupFixture();
    const escaped = { ...geometry, edges: geometry.edges.map((e) => e.id !== "ab" ? e : { ...e, sections: e.sections.map((s) => ({ ...s,
      points: s.points.map((p, i) => i === 1 || i === 2 ? { ...p, y: 30 } : p) })) }) };
    expect(validateGeometry(graph, escaped).diagnostics.map((d) => d.code)).toContain("feedback-containment");
    const acyclic = { ...graph, edges: graph.edges.filter((e) => e.id !== "ba") }, withoutReturn = { ...geometry, edges: geometry.edges.filter((e) => e.id !== "ba") };
    expect(validateGeometry(acyclic, withoutReturn).diagnostics.map((d) => d.code)).toContain("invalid-scc");
    const unknownParent = { ...geometry, nodes: geometry.nodes.map((n) => n.id === "a" ? { ...n, parentId: "missing" } : n) };
    expect(validateGeometry(graph, unknownParent).diagnostics.map((d) => d.code)).toContain("group-parent");
  });
  it("treats another group's empty interior as an obstacle for unrelated routes", () => {
    const { graph, geometry } = groupFixture();
    const additions: MeasuredNode[] = ["d", "e"].map((id) => ({ id, kind: "concept", width: 20, height: 20, labelBoxes: [], ports: [{ id: id + ":p", nodeId: id, semanticEndpointId: id,
      side: id === "d" ? "north" : "south", mode: "fixed-position", offset: { x: 10, y: id === "d" ? 0 : 20 } }] }));
    const withEdge = { ...graph, nodes: [...graph.nodes, ...additions], edges: [...graph.edges, { id: "de", sourcePortId: "d:p", targetPortId: "e:p", kind: "import", minRankSpan: 1 }] };
    const extra: GraphGeometry = { ...geometry, nodes: [...geometry.nodes, { id: "d", x: 230, y: 200, width: 20, height: 20, rank: 0 }, { id: "e", x: 230, y: 0, width: 20, height: 20, rank: 1 }],
      ports: [...geometry.ports, { id: "d:p", nodeId: "d", x: 240, y: 200 }, { id: "e:p", nodeId: "e", x: 240, y: 20 }],
      edges: [...geometry.edges, { id: "de", sections: [{ id: "de:route", points: [{ x: 240, y: 200 }, { x: 240, y: 180 }, { x: 210, y: 180 }, { x: 210, y: 28 }, { x: 240, y: 28 }, { x: 240, y: 20 }], nextSectionIds: [], terminalTargetPortId: "e:p" }] }] };
    const checked = validateGeometry(withEdge, extra);
    expect(checked.diagnostics.map((d) => d.code)).toContain("nonincident-group");
    expect(checked.diagnostics.map((d) => d.code)).not.toContain("obstacle-collision");
  });
});
