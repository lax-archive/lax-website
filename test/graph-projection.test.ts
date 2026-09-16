import fs from "node:fs";
import { describe, expect, it } from "vitest";
import { canonicalJson, compareText } from "../src/graph-layout/normalize.js";
import { indexedGraph, stronglyConnectedComponents } from "../src/graph-layout/components.js";
import { measureDisplayGraph, projectGraph, type DisplayGraph, type GraphKind, type ProofGraphData, type StatementGraphInput } from "../src/sitegen/graph-project.js";
import { displayLabelRequests } from "../src/sitegen/graph-node-size.js";
import { dockInkFixture } from "./fixtures/graph-layout/dock-ink.js";
import { graphInteractionPayload, graphSvg } from "../src/sitegen/graph-svg.js";
import { layoutGraph } from "../src/graph-layout/index.js";
import { validateGeometry } from "../src/graph-layout/validate.js";

const proofInput = (): ProofGraphData => ({ statements: [
  { id: "c.s1", concept: "c", index: 1, count: 2, title: "The concept", href: "c.html#s-1", proven: true },
  { id: "c.s2", concept: "c", index: 2, count: 2, title: "The concept", href: "c.html#s-2", proven: false },
  { id: "d.s", concept: "d", index: 1, count: 1, title: "The conclusion", href: "d.html" },
], proofs: [
  { id: "p1", assumptions: ["c.s1", "c.s2"], conclusion: "d.s" },
  { id: "p2", assumptions: ["c"], conclusion: "d.s" },
] });
const exactFixtureMetrics = { width: 120, height: 14, lines: [{ text: "Test fixture", x: 0, y: 11, ink: { x: 0, y: 1, width: 120, height: 13 } }] };
const fixtureLabels = (display: DisplayGraph) => new Map(displayLabelRequests([display]).map(({ text }) => [text,
  { ...exactFixtureMetrics, lines: exactFixtureMetrics.lines.map((line) => ({ ...line, text })) }]));

describe("semantic display projection", () => {
  it("coarsens multi-statement assumptions to one concept edge and shared outgoing port", () => {
    const projected = projectGraph("proofs", proofInput());
    expect(projected.nodes.filter((n) => n.kind === "proof")).toHaveLength(2);
    expect(projected.edges).toHaveLength(4);
    const concept = projected.nodes.find((n) => n.id === "c:c")!;
    expect(concept.label).toBe("c");
    expect(projected.nodes.find((n) => n.id === "s:d.s")!.label).toBe("d");
    expect(concept.docks.map((d) => [d.statementId, d.ordinal])).toEqual([["c.s1", 1], ["c.s2", 2]]);
    expect(concept.ports.map((p) => p.semanticEndpointId)).toEqual(["c"]);
    const measured = measureDisplayGraph(projected, fixtureLabels(projected));
    const docks = measured.graph.nodes.find((n) => n.id === concept.id)!.ports;
    const interaction = graphInteractionPayload(measured);
    expect(Object.keys(interaction.edges)).toHaveLength(4);
    expect(interaction.nodes["c:c"]).toMatchObject({ kind: "concept", semanticId: "c", nodeId: "c:c" });
    expect(interaction.nodes["dock:c.s1"]).toMatchObject({ kind: "dock", semanticId: "c.s1", nodeId: "c:c" });
    expect(interaction.edges["e:p1:assumption:c:0"]).toMatchObject({
      source: "c:c", target: "p:p1", sourceSemanticId: "c", targetSemanticId: "p1", kind: "assumption",
      semanticIds: ["p1:assumption:c.s1", "p1:assumption:c.s2"],
    });
    expect(projected.edges.filter((edge) => edge.kind === "assumption").map((edge) => edge.sourcePortId))
      .toEqual(["c:c:assumption-source", "c:c:assumption-source"]);
    expect(projected.mapping.find((entry) => entry.semanticId === "p1:assumption:c.s2")?.edgeIds)
      .toEqual(["e:p1:assumption:c:0"]);
    expect(docks.every((p) => p.mode === "fixed-position")).toBe(true);
    expect(new Set(docks.map((p) => p.offset!.x)).size).toBe(1);
    const { geometry } = layoutGraph(measured.graph, { inputDigest: "shared-concept-output" });
    expect(validateGeometry(measured.graph, geometry)).toMatchObject({ valid: true });
    expect(geometry.ports.filter((port) => port.id === "c:c:assumption-source")).toHaveLength(1);
  });
  it("shortens only local dock tooltip labels while preserving full identifiers and links", () => {
    const concepts = [{ id: "Lax701.Local", ext: false }, { id: "Lax702.Foreign", ext: true }];
    const statements = concepts.flatMap((concept) => ["first", "second"].map((name, index) => ({
      id: `${concept.id}.${name}`, concept: concept.id, ext: concept.ext,
      index: index + 1, count: 2, href: `${concept.id}.html#s-${concept.id}.${name}`,
    })));
    const display = projectGraph("proofs", { statements, proofs: [] });
    const interaction = graphInteractionPayload(measureDisplayGraph(display, fixtureLabels(display)));
    for (const statement of statements) {
      expect(interaction.nodes[`dock:${statement.id}`]).toMatchObject({
        label: statement.ext ? statement.id : `Local.${statement.id.split(".").at(-1)}`,
        semanticId: statement.id, href: statement.href,
      });
    }
  });
  it("scales node envelopes, ink, docks and attachments together without changing graph semantics", () => {
    const original = projectGraph("proofs", proofInput());
    const display = projectGraph("proofs", { ...proofInput(), nodeScale: 1.25 });
    const labels = fixtureLabels(original);
    const baseline = measureDisplayGraph(original, labels), enlarged = measureDisplayGraph(display, labels);
    expect(projectGraph("proofs", { ...proofInput(), nodeScale: 1 })).toEqual(original);
    expect(displayLabelRequests([display])).toEqual(displayLabelRequests([original]));
    expect(enlarged.drawings).toEqual(baseline.drawings);
    expect(enlarged.graph.edges).toEqual(baseline.graph.edges);
    expect(graphInteractionPayload(enlarged)).toEqual(graphInteractionPayload(baseline));
    const scaleRect = (box: { x: number; y: number; width: number; height: number }) => ({
      x: box.x * 1.25, y: box.y * 1.25, width: box.width * 1.25, height: box.height * 1.25,
    });
    for (const [index, node] of enlarged.graph.nodes.entries()) {
      const before = baseline.graph.nodes[index]!;
      expect(node.width).toBe(before.width * 1.25);
      expect(node.height).toBe(before.height * 1.25);
      expect(node.labelBoxes).toEqual(before.labelBoxes.map(scaleRect));
      expect(node.footprints).toEqual(before.footprints!.map((footprint) => ({ ...footprint, bounds: scaleRect(footprint.bounds) })));
      expect(node.ports).toEqual(before.ports.map((port) => port.offset ? { ...port,
        offset: { x: port.offset.x * 1.25, y: port.offset.y * 1.25 } } : port));
    }
    const { geometry } = layoutGraph(enlarged.graph, { inputDigest: "scaled-node-fixture" });
    expect(validateGeometry(enlarged.graph, geometry).valid).toBe(true);
    expect(graphSvg(enlarged, geometry, "scaled").match(/ scale\(1\.25\)/g)).toHaveLength(display.nodes.length);
  });
  it.each([0, 0.5, 5, NaN, Infinity])("rejects an invalid node scale (%s)", (nodeScale) => {
    expect(() => projectGraph("proofs", { ...proofInput(), nodeScale })).toThrow(/graph-node-scale/);
  });
  it("measures dock ink, preserves fixed statement attachments, and diagnoses absent ordinal metrics", () => {
    const display = dockInkFixture(), labels = fixtureLabels(display);
    labels.set("1", { width: 6, height: 16, lines: [{ text: "1", x: 0, y: 12, ink: { x: 0.5, y: 2, width: 5, height: 12 } }] });
    labels.set("9876543210", { width: 60, height: 16, lines: [{ text: "9876543210", x: 0, y: 12, ink: { x: 0.5, y: 2, width: 59, height: 12 } }] });
    const measured = measureDisplayGraph(display, labels), node = measured.graph.nodes.find((n) => n.id === "c:Claims")!;
    const drawing = measured.drawings.get(node.id)!;
    const inspector = graphInteractionPayload(measured);
    expect(drawing.docks[0]!.bounds.width).toBeGreaterThanOrEqual(20);
    expect(drawing.docks[1]!.bounds.width).toBeGreaterThan(60);
    expect(node.labelBoxes).toHaveLength(drawing.lines.length + 2);
    for (const dock of drawing.docks) {
      expect(inspector.nodes[dock.id]!.label).toBe(dock.statementId);
      expect(inspector.nodes[dock.id]!.tooltipHtml).toBeUndefined();
      const port = node.ports.find((p) => p.semanticEndpointId === dock.statementId)!;
      expect(port.mode).toBe("fixed-position");
      expect(port.offset!.x).toBeCloseTo(dock.bounds.x + dock.bounds.width / 2, 2);
      expect(node.labelBoxes).toContainEqual(dock.lines[0]!.ink);
      expect(dock.lines[0]!.text).toBe(String(dock.ordinal));
      expect(dock.bounds.y).toBeLessThan(drawing.body.y + drawing.body.height);
      expect(dock.bounds.y + dock.bounds.height).toBeGreaterThan(drawing.body.y + drawing.body.height);
      expect(dock.bounds.height).toBe(dock.bounds.width);
      expect(port.offset!.y).toBe(dock.bounds.y);
      expect(dock.lines[0]!.y).toBeCloseTo(dock.bounds.y + (dock.bounds.height - 16) / 2 + 12);
    }
    expect(displayLabelRequests([display, display])).toEqual(displayLabelRequests([{ ...display, nodes: [...display.nodes].reverse() }]));
    expect(displayLabelRequests([display]).map((request) => request.text)).not.toContain("⊢");
    labels.delete("9876543210");
    expect(() => measureDisplayGraph(display, labels)).toThrow(/missing-dock-metrics/);
  });
  it.each([
    { name: "boundary sum", labelHeight: 6.0151, dockDiagonal: 72, dockInkHeight: 57.6, expectedHeight: 100.016 },
    { name: "fractional dock", labelHeight: 6, dockDiagonal: 36.0001, dockInkHeight: 12, expectedHeight: 64.001 },
  ])("keeps rounded conclusion ports inside their node for $name measurements", ({ labelHeight, dockDiagonal, dockInkHeight, expectedHeight }) => {
    const display: DisplayGraph = { kind: "proofs", mapping: [], nodes: [
      { id: "p:proof", semanticId: "proof", kind: "proof", label: "⊢", status: "none", ext: false, docks: [], ports: [
        { id: "proof:out", nodeId: "p:proof", semanticEndpointId: "proof", side: "north", mode: "free-on-side" },
      ] },
      { id: "c:conclusion", semanticId: "conclusion", kind: "concept", label: "Conclusion", status: "open", ext: false,
        docks: [{ id: "dock:conclusion", statementId: "conclusion.statement", ordinal: 1, status: "open" }], ports: [
          { id: "conclusion:in", nodeId: "c:conclusion", semanticEndpointId: "conclusion.statement", side: "south", mode: "free-on-side" },
        ] },
    ], edges: [
      { id: "conclusion", sourcePortId: "proof:out", targetPortId: "conclusion:in", kind: "conclusion", minRankSpan: 1 },
    ] };
    const dockLabelHeight = Math.max(14, dockInkHeight);
    const labels = new Map<string, GraphLabel>([
      ["Conclusion", { width: 20, height: labelHeight,
        lines: [{ text: "Conclusion", x: 0, y: labelHeight, ink: { x: 0, y: 0, width: 20, height: labelHeight } }] }],
      ["1", { width: Math.sqrt(dockDiagonal ** 2 - dockInkHeight ** 2), height: dockLabelHeight,
        lines: [{ text: "1", x: 0, y: dockLabelHeight, ink: { x: 0, y: 0, width: 6, height: dockInkHeight } }] }],
    ]);

    const measured = measureDisplayGraph(display, labels);
    const conclusion = measured.graph.nodes.find((node) => node.id === "c:conclusion")!;
    const port = conclusion.ports.find((candidate) => candidate.id === "conclusion:in")!;
    expect(conclusion.height).toBe(expectedHeight);
    expect(port.offset!.y).toBe(conclusion.height);
    expect(validateGeometry(measured.graph, layoutGraph(measured.graph, { inputDigest: "rounded-conclusion-port" }).geometry).valid).toBe(true);
  });
  it("never renumbers missing docks or silently deletes missing endpoints", () => {
    const input = proofInput();
    expect(() => projectGraph("proofs", { ...input, statements: input.statements.slice(1) })).toThrow(/incomplete-docks/);
    expect(() => projectGraph("proofs", { ...input, proofs: [{ id: "p", assumptions: ["absent"], conclusion: "d.s" }] })).toThrow(/missing-semantic-endpoint/);
  });
  it("allows dock adapters inside their attachment area while still protecting labels and unrelated incidences", () => {
    const display = dockInkFixture();
    const measured = measureDisplayGraph(display, fixtureLabels(display));
    const { geometry } = layoutGraph(measured.graph, { inputDigest: "dock-attachment-area" });
    expect(validateGeometry(measured.graph, geometry).valid).toBe(true);
    const foreignDocks = { ...measured.graph, nodes: measured.graph.nodes.map((node) => ({ ...node,
      footprints: node.footprints?.map((f) => f.kind === "dock" ? { ...f, semanticEndpointId: "unrelated" } : f),
    })) };
    expect(validateGeometry(foreignDocks, geometry).diagnostics.some((d) =>
      d.code === "obstacle-collision" && d.message.includes("attachment-area"))).toBe(true);
    const obstructed = { ...measured.graph, nodes: measured.graph.nodes.map((node) => ({ ...node,
      labelBoxes: [...node.labelBoxes, ...(node.footprints ?? []).filter((f) => f.kind === "attachment-area").map((f) => f.bounds)],
    })) };
    expect(validateGeometry(obstructed, geometry).diagnostics.some((d) =>
      d.code === "obstacle-collision" && d.message.includes("label"))).toBe(true);
  });
  it("preserves parallel direct import edges and ignores source array order", () => {
    const input = { nodes: [{ id: "a", title: "A" }, { id: "b", title: "B" }], edges: [{ from: "a", to: "b" }, { from: "a", to: "b" }] };
    const projected = projectGraph("concepts", input);
    expect(projected.edges).toHaveLength(2);
    expect(new Set(projected.edges.map((edge) => edge.id)).size).toBe(2);
    expect(canonicalJson(projectGraph("concepts", { nodes: [...input.nodes].reverse(), edges: [...input.edges].reverse() }))).toBe(canonicalJson(projected));
  });
  it("keeps source/private metadata out of display and geometry payloads", () => {
    const input = { nodes: [{ id: "a", title: "Public label", source: "secret-repository", authors: ["Private Person"], href: "a.html" }], edges: [] };
    const projected = projectGraph("concepts", input);
    expect(canonicalJson(projected)).not.toMatch(/secret-repository|Private Person|authors|source"/);
    const measured = measureDisplayGraph(projected, new Map([["Public label", exactFixtureMetrics]]));
    expect(canonicalJson(measured.graph)).not.toMatch(/Public label|href|secret-repository/);
    expect(() => projectGraph("concepts", { nodes: [{ id: "x", href: "https://private.example/repo" }], edges: [] })).toThrow(/graph-link/);
  });
  it("retains a display-only cycle created by grouping an acyclic statement graph", () => {
    const input: ProofGraphData = { statements: [
      { id: "c.a", concept: "c", index: 1, count: 2 }, { id: "c.b", concept: "c", index: 2, count: 2 },
    ], proofs: [{ id: "p", assumptions: ["c.a"], conclusion: "c.b" }] };
    const display = projectGraph("proofs", input);
    const measured = measureDisplayGraph(display, fixtureLabels(display));
    const graph = indexedGraph(measured.graph);
    expect(stronglyConnectedComponents(graph.nodeCount, graph.edges).some((members) => members.length === 2)).toBe(true);
    expect(measured.graph.edges).toHaveLength(2);
    const concept = measured.graph.nodes.find((node) => node.id === "c:c")!;
    expect(concept.ports.find((port) => port.side === "north")?.semanticEndpointId).toBe("c");
    expect(concept.ports.find((port) => port.side === "south")?.semanticEndpointId).toBe("c.b");
  });
  it("retains every semantic incidence while coarsening visual concept uses in the frozen real corpus", () => {
    const corpus = JSON.parse(fs.readFileSync("test/fixtures/graph-layout/corpus.json", "utf8"));
    let graphs = 0;
    for (const fixture of corpus.graphs) {
      const display = projectGraph(fixture.kind as GraphKind, fixture.data);
      if (fixture.kind === "proofs") {
        const assumptionSource = new Map<string, string>(fixture.data.statements
          .filter((statement: StatementGraphInput) => (statement.count ?? 1) > 1)
          .map((statement: StatementGraphInput) => [statement.id, statement.concept!]));
        const visualEdges = fixture.data.proofs.reduce((sum: number, proof: { assumptions: string[] }) =>
          sum + new Set(proof.assumptions.map((assumption) => assumptionSource.get(assumption) ?? assumption)).size + 1, 0);
        expect(display.edges.length).toBe(visualEdges);
        const exactIncidences = fixture.data.proofs.flatMap((proof: { id: string; assumptions: string[]; conclusion: string }) => [
          ...proof.assumptions.map((assumption) => `${proof.id}:assumption:${assumption}`),
          `${proof.id}:conclusion:${proof.conclusion}`,
        ]).sort(compareText);
        expect(display.edges.flatMap((edge) => edge.semanticIds ?? []).sort(compareText)).toEqual(exactIncidences);
      } else expect(display.edges.length).toBe(fixture.data.edges.length);
      const measured = measureDisplayGraph(display, fixtureLabels(display));
      expect(measured.graph.nodes.length).toBe(display.nodes.length);
      graphs++;
    }
    expect(graphs).toBe(1516);
  });
});
