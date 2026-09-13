import fs from "node:fs";
import { describe, expect, it } from "vitest";
import { canonicalJson } from "../src/graph-layout/normalize.js";
import { indexedGraph, stronglyConnectedComponents } from "../src/graph-layout/components.js";
import { measureDisplayGraph, projectGraph, type DisplayGraph, type GraphKind, type ProofGraphData } from "../src/sitegen/graph-project.js";
import { displayLabelRequests } from "../src/sitegen/graph-node-size.js";
import { dockInkFixture } from "./fixtures/graph-layout/dock-ink.js";

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
  it("preserves proof AND/OR incidence, exact statements, coarse assumptions, and fixed numbered docks", () => {
    const projected = projectGraph("proofs", proofInput());
    expect(projected.nodes.filter((n) => n.kind === "proof")).toHaveLength(2);
    expect(projected.edges).toHaveLength(5);
    const concept = projected.nodes.find((n) => n.id === "c:c")!;
    expect(concept.label).toBe("c");
    expect(projected.nodes.find((n) => n.id === "s:d.s")!.label).toBe("d");
    expect(concept.docks.map((d) => [d.statementId, d.ordinal])).toEqual([["c.s1", 1], ["c.s2", 2]]);
    expect(concept.ports.map((p) => p.semanticEndpointId).sort()).toEqual(["c", "c.s1", "c.s2"]);
    const measured = measureDisplayGraph(projected, fixtureLabels(projected));
    const docks = measured.graph.nodes.find((n) => n.id === concept.id)!.ports;
    expect(docks.every((p) => p.mode === "fixed-position")).toBe(true);
    expect(new Set(docks.map((p) => p.offset!.x)).size).toBe(3);
  });
  it("measures dock ink, preserves fixed statement attachments, and diagnoses absent ordinal metrics", () => {
    const display = dockInkFixture(), labels = fixtureLabels(display);
    labels.set("1", { width: 6, height: 16, lines: [{ text: "1", x: 0, y: 12, ink: { x: 0.5, y: 2, width: 5, height: 12 } }] });
    labels.set("9876543210", { width: 60, height: 16, lines: [{ text: "9876543210", x: 0, y: 12, ink: { x: 0.5, y: 2, width: 59, height: 12 } }] });
    const measured = measureDisplayGraph(display, labels), node = measured.graph.nodes.find((n) => n.id === "c:Claims")!;
    const drawing = measured.drawings.get(node.id)!;
    expect(drawing.docks[0]!.bounds.width).toBeGreaterThanOrEqual(20);
    expect(drawing.docks[1]!.bounds.width).toBeGreaterThan(60);
    expect(node.labelBoxes).toHaveLength(drawing.lines.length + 2);
    for (const dock of drawing.docks) {
      const port = node.ports.find((p) => p.semanticEndpointId === dock.statementId)!;
      expect(port.mode).toBe("fixed-position");
      expect(port.offset!.x).toBeCloseTo(dock.bounds.x + dock.bounds.width / 2, 2);
      expect(node.labelBoxes).toContainEqual(dock.lines[0]!.ink);
      expect(dock.lines[0]!.text).toBe(String(dock.ordinal));
      expect(dock.bounds.y).toBeGreaterThan(drawing.body.y + drawing.body.height);
      expect(dock.bounds.height).toBe(dock.bounds.width);
      expect(port.offset!.y).toBe(dock.bounds.y);
      expect(dock.lines[0]!.y).toBeCloseTo(dock.bounds.y + (dock.bounds.height - 16) / 2 + 12);
    }
    expect(displayLabelRequests([display, display])).toEqual(displayLabelRequests([{ ...display, nodes: [...display.nodes].reverse() }]));
    expect(displayLabelRequests([display]).map((request) => request.text)).not.toContain("⊢");
    labels.delete("9876543210");
    expect(() => measureDisplayGraph(display, labels)).toThrow(/missing-dock-metrics/);
  });
  it("never renumbers missing docks or silently deletes missing endpoints", () => {
    const input = proofInput();
    expect(() => projectGraph("proofs", { ...input, statements: input.statements.slice(1) })).toThrow(/incomplete-docks/);
    expect(() => projectGraph("proofs", { ...input, proofs: [{ id: "p", assumptions: ["absent"], conclusion: "d.s" }] })).toThrow(/missing-semantic-endpoint/);
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
  });
  it("round-trips every incidence in the frozen real corpus", () => {
    const corpus = JSON.parse(fs.readFileSync("test/fixtures/graph-layout/corpus.json", "utf8"));
    let graphs = 0;
    for (const fixture of corpus.graphs) {
      const display = projectGraph(fixture.kind as GraphKind, fixture.data);
      const expected = fixture.kind === "proofs" ? fixture.data.proofs.reduce((sum: number, proof: { assumptions: string[] }) => sum + proof.assumptions.length + 1, 0) : fixture.data.edges.length;
      expect(display.edges.length).toBe(expected);
      const measured = measureDisplayGraph(display, fixtureLabels(display));
      expect(measured.graph.nodes.length).toBe(display.nodes.length);
      graphs++;
    }
    expect(graphs).toBe(1516);
  });
});
