import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { describe, expect, it } from "vitest";
import { canonicalJson } from "../src/graph-layout/normalize.js";
import { graphMeasurementKey, GraphMeasurementUnavailableError,
  type GraphMeasurerOptions, type MeasureLabelsProvider } from "../src/sitegen/graph-measure.js";
import { prepareGraphs, publicGraphPayload } from "../src/sitegen/graph-prepare.js";

const provider: MeasureLabelsProvider = async (requests, env) => requests.map((request) => {
  // Explicit geometry for these test labels only. No estimating provider is
  // accepted by the archive path; real browser measurement has separate tests.
  const widths = new Map([["Alpha", 31.734375], ["Beta", 24.953125], ["Gamma", 37.859375], ["A.s", 18], ["B.s", 18]]);
  const width = widths.get(request.text);
  if (width === undefined) throw new Error(`Unexpected fixture label ${request.text}`);
  return { text: request.text, width, height: 16, signature: graphMeasurementKey(request, env.signature),
    lines: [{ text: request.text, x: 0, y: 12, ink: { x: 0, y: 2, width, height: 12 } }] };
});
const measurement: GraphMeasurerOptions = { provider, providerId: "graph-preparation-exact-fixtures-v1" };
function data() {
  return {
    concepts: { home: "lax-1", nodes: [
      { id: "A", title: "Alpha", href: "A.html", dir: "core", owner: "lax-1", status: "proven" },
      { id: "B", title: "Beta", href: "B.html", dir: "up", ext: true, owner: "lax-2", status: "none" },
      { id: "C", title: "Gamma", href: "C.html", dir: "down", ext: true, owner: "lax-3", status: "open" },
    ], edges: [{ from: "B", to: "A" }, { from: "A", to: "C" }, { from: "B", to: "C" }] },
    submissions: { nodes: [
      { id: "lax-1", title: "Alpha", href: "index.html", dir: "core", state: "registered", concepts: 1, proofs: 1 },
      { id: "lax-2", title: "Beta", href: "../lax-2/index.html", dir: "up", state: "draft", concepts: 1, proofs: 1 },
    ], edges: [{ from: "lax-2", to: "lax-1", kind: "concepts" }] },
    proofs: { home: "lax-1", statements: [
      { id: "A.s", label: "A.s", concept: "A", title: "Alpha", index: 1, count: 1, proven: true, href: "A.html#s-A.s" },
      { id: "B.s", label: "B.s", concept: "B", title: "Beta", index: 1, count: 1, proven: true, href: "B.html#s-B.s" },
    ], proofs: [{ id: "P", assumptions: ["B.s"], conclusion: "A.s", href: "P.html", description: "A permitted proof description", tooltipHtml: "A <em>permitted</em> proof description", owner: "lax-1", assumptionsProven: true, outstanding: 0 }],
    details: { "concept:A": { kind: "concept", name: "Alpha", status: "proven", href: "A.html",
      reviewUrl: "https://laxarchive.org/lax-1/A.html", statements: [{ id: "A.s", name: "Lean statement", signature: "A.s : True", proven: true }] } } },
  };
}
function page(payload: unknown, kinds = ["concepts", "proofs", "submissions"]): string {
  const containers: Record<string, string> = {
    concepts: '<figure class="graph-figure"><button id="concept-expand" aria-pressed="true">Hide ancestors</button><button id="concept-descend" aria-pressed="false">Show descendants</button><output id="concept-graph-status"></output><div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div></figure>',
    proofs: '<figure class="graph-figure proof-network-figure"><div id="proof-network" class="figure-container" data-graph="proofs"></div></figure>',
    submissions: '<figure class="graph-figure"><div id="submission-dag" class="figure-container" data-graph="submissions"></div></figure>',
  };
  return '<!doctype html><html><head><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; script-src \'self\'; style-src \'self\' \'unsafe-inline\'; font-src \'self\'; connect-src https://account.example"></head><body>' +
    kinds.map((kind) => containers[kind]).join("") +
    '<script type="application/json" id="graph-data">' + JSON.stringify(payload).replace(/</gu, "\\u003c") + '</script>' +
    '<script src="../assets/layout.js?v=old"></script><script src="../assets/dag.js?v=old"></script></body></html>';
}
function payload(html: string): Record<string, any> {
  return JSON.parse(/<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/u.exec(html)![1]!);
}
function cacheFiles(root: string, extension = ".json"): string[] {
  return fs.readdirSync(root, { withFileTypes: true }).flatMap((entry) => entry.isDirectory()
    ? cacheFiles(path.join(root, entry.name), extension) : entry.name.endsWith(extension) ? [path.join(root, entry.name)] : []);
}

describe("prepared static graphs", () => {
  it("renders every graph kind before interaction, with complete semantic proof incidence and view counts", async () => {
    const files = new Map<string, string | Buffer>([["lax-1/index.html", page(data())]]);
    const report = await prepareGraphs(files, { measurement });
    const html = String(files.get("lax-1/index.html")), graph = payload(html);
    expect(report.localFallback).toBe(false);
    expect(report.statistics.containers).toBe(3);
    expect(report.statistics.views).toBe(6);
    expect(report.statistics.measurement?.uniqueLabels).toBe(5);
    expect(html.match(/<svg\b/gu)).toHaveLength(3);
    expect(html).toContain('class="prepared-graph"');
    expect(html).toContain('href="P.html"');
    expect(html).toContain('data-node-id="p:P"');
    expect(html).toContain('data-edge-id="e:P:assumption:B.s:0"');
    expect(html).toContain('data-edge-id="e:P:conclusion:A.s:0"');
    expect(html).toContain('data-edge-hit="e:P:conclusion:A.s:0"');
    expect(html).toMatch(/id="proof-network"[\s\S]*?<svg[^>]* width="720"/u);
    expect(html).toContain('style="height:');
    expect(html).not.toContain("assets/layout.js");
    expect(html).not.toContain("assets/dag.js");
    expect(html).not.toContain("graph-measure-local.js");
    expect(html).not.toContain("graph-local.js");
    expect(html.match(/src="[^"]*graph-interaction\.js\?v=/gu)).toHaveLength(1);
    expect(html).not.toContain("worker-src");
    expect(graph.prepared["concept-dag"]).toMatchObject({ initial: "10", ancestors: 1, descendants: 1 });
    expect(Object.keys(graph.prepared["concept-dag"].views)).toEqual(["10", "11", "00", "01"]); // Integer-like keys precede other object keys in JSON.
    expect(graph.prepared["concept-dag"].views["10"].svg).toBeUndefined();
    expect(graph.prepared["concept-dag"].views["10"].status).toBe("2 concepts; 1 descendant hidden");
    expect(graph.prepared["concept-dag"].views["11"].svg).toContain("e:B-&gt;C:import:0");
    expect(graph.proofs.proofs[0]).toMatchObject({ id: "P", assumptions: ["B.s"], conclusion: "A.s", assumptionsProven: true, outstanding: 0 });
    expect(graph.proofs.details["concept:A"]).toMatchObject({ name: "Alpha", href: "A.html",
      statements: [{ id: "A.s", signature: "A.s : True", proven: true }] });
    expect(graph.prepared["proof-network"].views.default.interaction.edges["e:P:conclusion:A.s:0"])
      .toMatchObject({ source: "p:P", target: "s:A.s", kind: "conclusion" });
    expect(graph.submissions.nodes[0]).toMatchObject({ state: "registered", concepts: 1, proofs: 1 });
  });

  it("keeps cached geometry, alternates and hidden payloads free of source/private fields", async () => {
    const input = data() as ReturnType<typeof data> & Record<string, unknown>;
    input.privateSource = { author: "secret@example.test" };
    Object.assign(input.concepts, { sourceRepository: "https://private.example/repository" });
    Object.assign(input.concepts.nodes[0]!, { authors: ["Hidden Person"], sourceText: "PRIVATE_SOURCE" });
    Object.assign(input.proofs.proofs[0]!, { privateView: "PRIVATE_VIEW", orcid: "0000-0000-0000-0000" });
    const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), "lax-prepare-private-"));
    const files = new Map<string, string | Buffer>([["previews/nested/lax-1/index.html", page(input)]]);
    const report = await prepareGraphs(files, { cacheDir, measurement, alternateInlineLimit: 0 });
    expect(report.statistics.alternateFiles).toBe(3);
    const graph = payload(String(files.get("previews/nested/lax-1/index.html")));
    expect(graph.prepared["concept-dag"].views["00"].src).toMatch(/^\.\.\/\.\.\/\.\.\/assets\/graph-views\/[a-f0-9]{64}\.json$/u);
    const all = [...files.values()].map(String).join("\n") + cacheFiles(cacheDir).map((file) => fs.readFileSync(file, "utf8")).join("\n");
    for (const forbidden of ["secret@example", "private.example", "Hidden Person", "PRIVATE_SOURCE", "PRIVATE_VIEW", "0000-0000-0000-0000", "sourceRepository", "privateSource"]) expect(all).not.toContain(forbidden);
    for (const file of cacheFiles(path.join(cacheDir, "geometry"))) {
      const geometry = fs.readFileSync(file, "utf8");
      expect(geometry).not.toMatch(/"(?:title|label|href|tooltipHtml|source|status)":/u);
    }
    const alternate = JSON.parse(String(files.get(graph.prepared["concept-dag"].views["00"].src.replace(/^(?:\.\.\/)+/u, ""))));
    expect(alternate.svg).toContain('href="A.html"');
    expect(alternate.interaction.nodes).toHaveProperty("c:A");
  });

  it("makes warm/cold output identical and remeasures invalid cached geometry", async () => {
    const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), "lax-prepare-cache-"));
    const original = page({ concepts: data().concepts }, ["concepts"]);
    const firstFiles = new Map<string, string | Buffer>([["index.html", original]]);
    const first = await prepareGraphs(firstFiles, { cacheDir, measurement, alternateInlineLimit: 0 });
    expect(first.statistics.layoutCacheMisses).toBe(4);
    const warmFiles = new Map<string, string | Buffer>([["index.html", original]]);
    const warm = await prepareGraphs(warmFiles, { cacheDir, measurement, alternateInlineLimit: 0 });
    expect(warm.statistics.layoutCacheHits).toBe(4);
    expect(canonicalJson([...warmFiles])).toBe(canonicalJson([...firstFiles]));
    const cache = cacheFiles(path.join(cacheDir, "geometry"))[0]!;
    const invalid = JSON.parse(fs.readFileSync(cache, "utf8"));
    // Even a well-formed, correctly checksummed record must pass independent
    // geometry validation: moving a box alone invalidates its attachments.
    invalid.geometry.nodes[0].x += 1000;
    invalid.geometryDigest = createHash("sha256").update(canonicalJson(invalid.geometry)).digest("hex");
    fs.writeFileSync(cache, JSON.stringify(invalid));
    const repairedFiles = new Map<string, string | Buffer>([["index.html", original]]);
    const repaired = await prepareGraphs(repairedFiles, { cacheDir, measurement, alternateInlineLimit: 0 });
    expect(repaired.statistics.corruptGeometryEntries).toBe(1);
    expect(repaired.statistics.layoutCacheMisses).toBe(1);
    expect(canonicalJson([...repairedFiles])).toBe(canonicalJson([...firstFiles]));
  });

  it("is invariant under nonsemantic input ordering and status decoration", async () => {
    const input = data(), reversed = data();
    reversed.concepts.nodes.reverse(); reversed.concepts.edges.reverse();
    reversed.proofs.statements.reverse();
    const a = new Map<string, string | Buffer>([["index.html", page(input)]]);
    const b = new Map<string, string | Buffer>([["index.html", page(reversed)]]);
    await prepareGraphs(a, { measurement, selfContained: true });
    await prepareGraphs(b, { measurement, selfContained: true });
    expect(String(a.get("index.html"))).toBe(String(b.get("index.html")));
    reversed.concepts.nodes[0]!.status = "proven";
    const decorated = new Map<string, string | Buffer>([["index.html", page(reversed)]]);
    const result = await prepareGraphs(decorated, { measurement });
    const initial = payload(String(a.get("index.html"))).prepared;
    const final = payload(String(decorated.get("index.html"))).prepared;
    expect(final["concept-dag"].views["11"].svg.match(/data-layout-digest="([^"]+)"/u)[1]).toBe(initial["concept-dag"].views["11"].svg.match(/data-layout-digest="([^"]+)"/u)[1]);
    expect(result.statistics.containers).toBe(3);
  });

  it("does not compute inapplicable closure states and embeds all self-contained views", async () => {
    const input = data().concepts;
    input.nodes = input.nodes.filter((node) => node.dir !== "down");
    input.edges = input.edges.filter((edge) => edge.to !== "C");
    const files = new Map<string, string | Buffer>([["index.html", page({ concepts: input }, ["concepts"])]]);
    await prepareGraphs(files, { measurement, selfContained: true, alternateInlineLimit: 0 });
    const html = String(files.get("index.html")), graph = payload(html).prepared["concept-dag"];
    expect(Object.keys(graph.views).sort()).toEqual(["00", "10"]);
    expect(graph.views["00"].svg).toContain("<svg");
    expect(html).toContain("No descendants</button>");
    expect(files.size).toBe(1);
  });

  it("diagnoses a missing hidden endpoint before filtering and never partially replaces the file map", async () => {
    const broken = data();
    broken.concepts.edges.push({ from: "MISSING", to: "C" });
    const files = new Map<string, string | Buffer>([["a.html", page(data())], ["b.html", page(broken)]]);
    const snapshot = canonicalJson([...files]);
    await expect(prepareGraphs(files, { measurement })).rejects.toThrow(/missing-semantic-endpoint/u);
    expect(canonicalJson([...files])).toBe(snapshot);
  });

  it("inserts dollar literals as data without replacement-string expansion", async () => {
    const input = data();
    input.proofs.proofs[0]!.id = "P$&";
    const text = "$& $$ $' $`";
    input.proofs.proofs[0]!.description = text;
    input.proofs.proofs[0]!.tooltipHtml = text;
    Object.assign(input, { privateSource: "DOLLAR_MUST_NOT_REINSERT_THIS" });
    const files = new Map<string, string | Buffer>([["index.html", page(input)]]);
    await prepareGraphs(files, { measurement });
    const html = String(files.get("index.html"));
    expect(payload(html).proofs.proofs[0].description).toBe(text);
    expect(html).toContain('data-node-id="p:P$&amp;"');
    expect(html.match(/id="graph-data"/gu)).toHaveLength(1);
    expect(html).not.toContain("DOLLAR_MUST_NOT_REINSERT_THIS");
  });

  it("uses the isolated local fallback only for unavailable host measurement", async () => {
    const unavailable: GraphMeasurerOptions = { providerId: "missing-test-host-v1", provider: async () => { throw new GraphMeasurementUnavailableError("no exact host is installed"); } };
    const input = { concepts: data().concepts, privateRepository: "NEVER_PUBLISH_ME" };
    const original = page(input, ["concepts"]);
    const archive = new Map<string, string | Buffer>([["nested/index.html", original]]);
    await expect(prepareGraphs(archive, { measurement: unavailable })).rejects.toBeInstanceOf(GraphMeasurementUnavailableError);
    expect(archive.get("nested/index.html")).toBe(original);
    const local = new Map<string, string | Buffer>([["nested/index.html", original]]);
    const report = await prepareGraphs(local, { mode: "local", measurement: unavailable });
    expect(report.localFallback).toBe(true);
    const html = String(local.get("nested/index.html")), descriptor = payload(html).local;
    expect(html).toContain("worker-src 'self'");
    expect(html).toContain("../assets/graph-measure-local.js?v=");
    expect(html).toContain("../assets/graph-local.js?v=");
    expect(html).not.toContain("assets/layout.js");
    expect(html).not.toContain("NEVER_PUBLISH_ME");
    expect(descriptor.environment.fontSignature).toMatch(/^[a-f0-9]{64}$/u);
    expect(descriptor.containers["concept-dag"].views["11"].display.edges).toHaveLength(3);
    expect(descriptor.containers["concept-dag"]).toMatchObject({ kind: "concepts", initial: "10", ancestors: 1, descendants: 1 });
    const invalidProvider: GraphMeasurerOptions = { providerId: "invalid-test-host-v1", provider: async () => { throw new Error("invalid font metrics"); } };
    await expect(prepareGraphs(new Map([["index.html", original]]), { mode: "local", measurement: invalidProvider })).rejects.toThrow("invalid font metrics");
  });

  it("returns a small no-op result without launching tooling on graphless pages", async () => {
    const files = new Map<string, string | Buffer>([["about.html", "<!doctype html><p>About</p>"]]);
    expect(await prepareGraphs(files)).toMatchObject({ localFallback: false, diagnostics: [], statistics: { pages: 0, views: 0, containers: 0 } });
    expect(files.get("about.html")).toBe("<!doctype html><p>About</p>");
    expect(publicGraphPayload({ concepts: data().concepts, private: "hidden" })).not.toHaveProperty("private");
    expect(() => publicGraphPayload({ proofs: { ...data().proofs,
      details: { "concept:A": { kind: "concept", name: "Alpha", href: "javascript:alert(1)" } } } }))
      .toThrow(/relative public page URL/u);
  });
});
