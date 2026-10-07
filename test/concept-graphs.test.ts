import { describe, expect, it } from "vitest";
import { conceptGraph } from "../src/sitegen/graphs.js";
import { SiteModel, type SiteSubmission } from "../src/sitegen/model.js";
import { MarkdownRenderer } from "../src/sitegen/markdown.js";
import { conceptPage } from "../src/sitegen/pages/concept.js";
import { submissionPage } from "../src/sitegen/pages/submission.js";
import { prepareGraphs } from "../src/sitegen/graph-prepare.js";
import { graphMeasurementKey, type MeasureLabelsProvider } from "../src/sitegen/graph-measure.js";

function submission(id: string, concepts: [string, string[]][]): SiteSubmission {
  return {
    record: { specVersion: "1", id, state: "registered", createdAt: "2026-01-01T00:00:00Z" },
    output: {
      specVersion: "1", id,
      manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "abc", title: "Alpha", authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
      concepts: concepts.map(([id, imports]) => ({
        id, imports, title: "Alpha", type: "definition", path: `concepts/${id.replaceAll(".", "/")}.lean`,
        description: "", mathlibImports: [], sourceText: "", statements: [],
      })),
    },
  };
}

function star(count: number): SiteModel {
  return new SiteModel([
    submission("Lax1", [["Lax1.Ancestor", []]]),
    submission("Lax2", [["Lax2.Root", ["Lax1.Ancestor"]]]),
    submission("Lax3", Array.from({ length: count }, (_, i) => [`Lax3.Child${i}`, ["Lax2.Root"]])),
  ]);
}

const downIds = (graph: ReturnType<typeof conceptGraph>) => graph.nodes.filter((node) => node.dir === "down").map((node) => node.id);

describe("concept descendant limit", () => {
  it.each([0, 9, 10, 11, 1000])("keeps the entire expansion only at or below ten descendants (%i)", (count) => {
    const graph = conceptGraph(star(count), ["Lax2.Root"]);
    expect(downIds(graph)).toHaveLength(count <= 10 ? count : 0);
    expect(graph.descendantsOmitted).toBe(count > 10 ? true : undefined);
    expect(graph.nodes.filter((node) => node.dir !== "down").map((node) => [node.id, node.dir]))
      .toEqual([["Lax1.Ancestor", "up"], ["Lax2.Root", "core"]]);
    const visible = new Set(graph.nodes.map((node) => node.id));
    expect(graph.edges.every((edge) => visible.has(edge.from) && visible.has(edge.to))).toBe(true);
  });

  it("counts transitive descendants even when the root has only one direct importer", () => {
    const model = new SiteModel([submission("Lax1", [
      ["Lax1.Root", []],
      ...Array.from({ length: 11 }, (_, i): [string, string[]] => [
        `Lax1.Child${i}`, [i ? `Lax1.Child${i - 1}` : "Lax1.Root"],
      ]),
    ])]);
    expect(model.importers.get("Lax1.Root")).toHaveLength(1);
    expect(downIds(conceptGraph(model, ["Lax1.Root"]))).toEqual([]);
    expect(downIds(conceptGraph(model, ["Lax1.Child0"]))).toHaveLength(10);
  });

  it("counts shared descendants once and excludes the root in cycles", () => {
    const model = new SiteModel([submission("Lax1", [
      ["Lax1.Root", ["Lax1.Shared0"]],
      ["Lax1.Left", ["Lax1.Root"]], ["Lax1.Right", ["Lax1.Root"]],
      ...Array.from({ length: 8 }, (_, i): [string, string[]] => [
        `Lax1.Shared${i}`, ["Lax1.Left", "Lax1.Right"],
      ]),
    ])]);
    expect(model.downstreamClosure("Lax1.Root")).toHaveLength(10);
    expect(conceptGraph(model, ["Lax1.Root"]).descendantsOmitted).toBeUndefined();
    expect(conceptGraph(model, ["Lax1.Root"]).nodes.find((node) => node.id === "Lax1.Root")?.dir).toBe("core");
  });

  it("applies the limit separately to roots and preserves core concepts", () => {
    const model = star(11);
    const small = submission("Lax4", [["Lax4.Root", []]]);
    const children = submission("Lax5", Array.from({ length: 10 }, (_, i) => [`Lax5.Child${i}`, ["Lax4.Root"]]));
    const combined = new SiteModel([...model.submissions, small, children]);
    const roots = ["Lax2.Root", "Lax4.Root", "Lax3.Child0"];
    const graph = conceptGraph(combined, roots);
    expect(downIds(graph)).toEqual(children.output!.concepts.map((concept) => concept.id).sort());
    expect(graph.nodes.filter((node) => node.dir === "core").map((node) => node.id).sort()).toEqual(roots.sort());
    expect(conceptGraph(combined, [...roots].reverse())).toEqual(graph);
  });

  it("stops a bounded traversal at eleven without changing the default full closure", () => {
    const model = star(1000);
    expect(model.downstreamClosure("Lax2.Root", 11)).toHaveLength(11);
    expect(model.downstreamClosure("Lax2.Root")).toHaveLength(1000);
  });

  it.each([10, 11])("prepares only permitted views on concept and submission pages (%i descendants)", async (count) => {
    const model = star(count), ctx = { model, markdown: new MarkdownRenderer(model) };
    const concept = await conceptPage(ctx, model.conceptHome.get("Lax2.Root")!);
    const submissionHtml = await submissionPage(ctx, model.submissionById.get("Lax2")!);
    const files = new Map<string, string | Buffer>([["Lax2/Lax2.Root.html", concept], ["Lax2/index.html", submissionHtml]]);
    // Literal metrics for this one fixture label; browser measurement is
    // covered separately by the integration suite.
    const provider: MeasureLabelsProvider = async (requests, environment) => requests.map((request) => {
      if (request.text !== "Alpha") throw new Error(`Unexpected fixture label ${request.text}`);
      return { text: request.text, width: 31.734375, height: 16,
        signature: graphMeasurementKey(request, environment.signature),
        lines: [{ text: request.text, x: 0, y: 12, ink: { x: 0, y: 2, width: 31.734375, height: 12 } }] };
    });
    await prepareGraphs(files, { measurement: { provider, providerId: "concept-limit-alpha-fixture-v1" } });
    for (const html of files.values()) {
      const source = String(html);
      const graph = JSON.parse(/<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/u.exec(source)![1]!);
      expect(graph.concepts.nodes).toHaveLength(count === 10 ? 12 : 2);
      expect(Object.keys(graph.prepared["concept-dag"].views).sort()).toEqual(count === 10 ? ["00", "01", "10", "11"] : ["00", "10"]);
      expect(graph.prepared["concept-dag"].descendants).toBe(count === 10 ? 10 : 0);
      expect(source).toMatch(count === 10
        ? /<button[^>]*id="concept-descend"[^>]*>Show descendants<\/button>/u
        : /<button[^>]*id="concept-descend"[^>]*disabled[^>]*>Descendants omitted<\/button>/u);
      expect(source.includes("Descendants are omitted for concepts with more than 10 descendants.")).toBe(count > 10);
      expect(source).not.toContain("No descendants</button>");
    }
  });
});
