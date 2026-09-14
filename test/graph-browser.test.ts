import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath, pathToFileURL } from "node:url";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { chromium, firefox, webkit, type Browser, type BrowserContextOptions, type Page } from "playwright-core";
import { SITE_MIME, siteAssetPath } from "../src/sitegen/assets.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { createGraphMeasurer, PINNED_GRAPH_BROWSER_VERSION } from "../src/sitegen/graph-measure.js";
import type { GraphPreparationResult } from "../src/sitegen/graph-prepare.js";
import { tmpDir } from "./helpers.js";
import { displayLabelRequests, measureDisplayGraph } from "../src/sitegen/graph-node-size.js";
import { graphSvg } from "../src/sitegen/graph-svg.js";
import { layoutGraph } from "../src/graph-layout/index.js";
import { dockInkFixture } from "./fixtures/graph-layout/dock-ink.js";

// Installing the renderer, or running the pure tests, never installs a browser.
// Archive CI explicitly supplies the same browser used for exact measurement.
const executable = process.env.GRAPH_CHROME;
const browserName = process.env.GRAPH_BROWSER ?? "chromium";
if (!["chromium", "firefox", "webkit"].includes(browserName)) throw new Error(`Unknown GRAPH_BROWSER ${browserName}`);
const runtimeBrowser = { chromium, firefox, webkit }[browserName as "chromium" | "firefox" | "webkit"];
const playwrightPackage = createRequire(import.meta.url).resolve("playwright-core/package.json");
const browserMetadata = JSON.parse(fs.readFileSync(path.join(path.dirname(playwrightPackage), "browsers.json"), "utf8"));
const runtimeVersion = browserName === "chromium" ? PINNED_GRAPH_BROWSER_VERSION
  : browserMetadata.browsers.find((browser: { name: string }) => browser.name === browserName).browserVersion;
const screenshotDirectory = process.env.GRAPH_SCREENSHOTS ? path.resolve(process.env.GRAPH_SCREENSHOTS) : undefined;
const repository = fileURLToPath(new URL("../", import.meta.url));
const mainPage = "Lax702/index.html";
const proofId = "p:Lax702Proofs.Main";

function fixture(): SiteSubmission[] {
  type Concept = NonNullable<SiteSubmission["output"]>["concepts"][number];
  type Proof = NonNullable<SiteSubmission["output"]>["proofs"][number];
  const concept = (id: string, title: string, imports: string[] = [], statements = 1): Concept => ({
    id, title, type: statements ? "theorem" : "definition", path: `concepts/${id.replaceAll(".", "/")}.lean`,
    description: "A graph browser fixture.", imports, mathlibImports: [],
    sourceText: `namespace ${id}\naxiom claim : True\nend ${id}\n`,
    statements: Array.from({ length: statements }, (_, i) => ({ id: `${id}.s${i + 1}`,
      signature: `s${i + 1} : True`, startLine: 2, endLine: 2, doc: "A checked claim." })),
  });
  const proof = (id: string, conclusion: string, assumptions: string[], description = "A direct proof."): Proof => ({
    id, conclusion, assumptions, description, path: `proofs/${id.replaceAll(".", "/")}.lean`,
  });
  const submission = (id: string, concepts: Concept[], proofs: Proof[], anonymous = false): SiteSubmission => ({
    record: { specVersion: "1", id, state: "registered", createdAt: "2026-01-01T00:00:00Z",
      source: { repository: `https://github.com/withheld-browser-source/${id}`, commit: "a".repeat(40), folder: "." } },
    output: { specVersion: "1", id, manifest: { specVersion: "1", id,
      title: id === "Lax702" ? `Graph fixture ${id} with $x^2$` : `Graph fixture ${id}`,
      leanVersion: "v4.30.0", mathlibVersion: "abc", anonymous, authors: [{ name: "Withheld Browser Author", github: "withheld-browser-author" }], bibEntries: [] },
    abstract: "A small deterministic integration fixture, not archive benchmark data.", requiredByConcepts: [], requiredByProofs: [], concepts, proofs },
  });
  const premises = Array.from({ length: 5 }, (_, i) => concept(`Lax702.Premise${i + 1}`,
    `Premise ${i + 1}: a measured long label with χ and K₃`, ["Lax701.Base"]));
  return [
    submission("Lax701", [concept("Lax701.Base", "Two foundational statements", [], 2)], [
      proof("Lax701Proofs.Base", "Lax701.Base.s1", []),
    ]),
    submission("Lax702", [...premises,
      concept("Lax702.Middle", "Intermediate $x^2$ conclusion", premises.map((c) => c.id)),
      concept("Lax702.Main", "Main χ result", ["Lax702.Middle", "Lax701.Base"]),
    ], [
      ...premises.map((c, i) => proof(`Lax702Proofs.Premise${i + 1}`, `${c.id}.s1`, [`Lax701.Base.s${i % 2 + 1}`])),
      proof("Lax702Proofs.Middle", "Lax702.Middle.s1", premises.map((c) => `${c.id}.s1`)),
      proof("Lax702Proofs.Main", "Lax702.Main.s1", ["Lax702.Middle.s1"],
        "The $x^2$ bound follows.\n\n$$\\sum_{i=1}^n i = n(n+1)/2.$$"),
      proof("Lax702Proofs.Alternative", "Lax702.Main.s1", ["Lax702.Premise1.s1"], "A distinct alternative proof."),
    ]),
    submission("Lax703", [concept("Lax703.Application", "A downstream application", ["Lax702.Main", "Lax701.Base"])], [
      proof("Lax703Proofs.Application", "Lax703.Application.s1", ["Lax702.Main.s1"]),
    ]),
    submission("Lax704", [concept("Lax704.Anonymous", "An anonymous result")], [
      proof("Lax704Proofs.Anonymous", "Lax704.Anonymous.s1", [], "An anonymous proof of $1=1$."),
    ], true),
  ];
}

type Audit = { requests: string[]; errors: string[]; releaseFonts: () => void; serverRequests: () => string[] };
async function animationFrame(page: Page): Promise<void> {
  await page.evaluate(() => new Promise<void>((resolve) => requestAnimationFrame(() => requestAnimationFrame(() => resolve()))));
}
async function openConcepts(page: Page): Promise<void> {
  const summary = page.locator("details").filter({ has: page.locator("#concept-dag") }).locator(":scope > summary");
  await summary.click();
}
async function fingerprint(page: Page, id = "proof-network"): Promise<unknown> {
  return page.locator(`#${id} svg.prepared-graph`).evaluate((svg) => ({
    digest: svg.getAttribute("data-layout-digest"), viewBox: svg.getAttribute("viewBox"),
    paths: [...svg.querySelectorAll("[data-edge-id]")].map((edge) => [edge.getAttribute("data-edge-id"), edge.getAttribute("d"), edge.getAttribute("marker-end")]),
    nodes: [...svg.querySelectorAll("[data-node-id]")].map((node) => [node.getAttribute("data-node-id"), node.parentElement?.getAttribute("transform"),
      [...node.querySelectorAll("rect,text")].map((el) => [el.tagName, el.getAttribute("x"), el.getAttribute("y"), el.getAttribute("width"), el.getAttribute("height"), el.textContent])]),
  }));
}
async function expectNoPublicLayout(page: Page, audit: Audit): Promise<void> {
  expect(audit.requests.filter((url) => /(?:\/graph-local\/|\/graph-local\.js|\/graph-measure-local\.js|\/layout\.js|\/dag\.js|elk(?:js)?|graphviz|cytoscape|dagre)/iu.test(url))).toEqual([]);
  expect(await page.evaluate(() => (window as any).__graphAudit.computation)).toEqual({ workers: 0, legacy: 0, textMeasurements: 0 });
}
async function expectLabelContainment(page: Page): Promise<void> {
  await page.evaluate(() => document.fonts.ready);
  const labels = await page.locator("svg.prepared-graph .graph-label, svg.prepared-graph .graph-dock-number").evaluateAll((elements) => elements.map((text) => {
    const ink = (text as SVGGraphicsElement).getBBox();
    const box = text.parentElement!.querySelector("rect, circle")!;
    const circle = box.tagName === "circle", radius = Number(box.getAttribute("r"));
    const x = circle ? Number(box.getAttribute("cx")) - radius : Number(box.getAttribute("x"));
    const y = circle ? Number(box.getAttribute("cy")) - radius : Number(box.getAttribute("y"));
    const width = circle ? 2 * radius : Number(box.getAttribute("width"));
    const height = circle ? 2 * radius : Number(box.getAttribute("height"));
    const style = getComputedStyle(text);
    return { text: text.textContent, contained: ink.x >= x - 0.02 && ink.y >= y - 0.02 && ink.x + ink.width <= x + width + 0.02 && ink.y + ink.height <= y + height + 0.02,
      nonempty: ink.width > 0 && ink.height > 0, family: style.fontFamily, size: style.fontSize };
  }));
  expect(labels.length).toBeGreaterThan(0);
  expect(labels.filter((label) => !label.contained || !label.nonempty)).toEqual([]);
  expect(labels.every((label) => label.family.includes("Latin Modern") && label.size === "12px")).toBe(true);
}
describe.skipIf(!executable && !process.env.GRAPH_BROWSER)(`published graph views and the packaged local renderer in ${browserName}`, () => {
  let browser: Browser, server: http.Server, origin: string, directory: string;
  let archive: string, exported: string;
  let archiveReport: GraphPreparationResult;
  const serverRequests: string[] = [];
  const screenshots: { state: string; file: string; viewport: { width: number; height: number } | null; layoutDigests: string[] }[] = [];
  const contexts = new Set<Awaited<ReturnType<Browser["newContext"]>>>();

  beforeAll(async () => {
    if (!executable) throw new Error("GRAPH_CHROME is required for canonical archive measurement, including Firefox/WebKit runtime tests");
    directory = tmpDir("lax-graph-browser-");
    archive = path.join(directory, "archive"); exported = path.join(directory, "export");
    const cacheDir = path.join(directory, "cache");
    await generateSite(fixture(), archive, { graphs: { mode: "archive", cacheDir,
      alternateInlineLimit: 0, measurement: { executablePath: executable } }, graphReport: (result) => { archiveReport = result; } });
    await generateSite(fixture(), exported, { graphs: { mode: "archive", cacheDir,
      selfContained: true, alternateInlineLimit: 0, measurement: { hostBrowser: false } } });
    browser = await runtimeBrowser.launch({ headless: true,
      executablePath: process.env.GRAPH_BROWSER_EXECUTABLE ?? (browserName === "chromium" ? executable : undefined),
      ...(browserName === "chromium" ? { args: ["--no-sandbox", "--font-render-hinting=none"], ignoreDefaultArgs: ["--hide-scrollbars"] } : {}) });
    expect(browser.version()).toBe(runtimeVersion);
    server = http.createServer((request, response) => {
      serverRequests.push(origin + request.url);
      const pathname = decodeURIComponent(new URL(request.url!, "http://localhost").pathname);
      const prefix = "/preview/graph-drawing/";
      if (!pathname.startsWith(prefix)) { response.writeHead(404); response.end(); return; }
      let file = path.resolve(directory, pathname.slice(prefix.length));
      if (!file.startsWith(directory + path.sep)) { response.writeHead(403); response.end(); return; }
      if (fs.existsSync(file) && fs.statSync(file).isDirectory()) file = path.join(file, "index.html");
      if (!fs.existsSync(file)) { response.writeHead(404); response.end(); return; }
      response.writeHead(200, { "Content-Type": SITE_MIME[path.extname(file)] ?? "application/octet-stream", "Cache-Control": "no-store" });
      fs.createReadStream(file).pipe(response);
    });
    await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
    origin = `http://127.0.0.1:${(server.address() as import("node:net").AddressInfo).port}`;
  }, 120_000);

  afterAll(async () => {
    for (const context of contexts) await context.close();
    await browser?.close();
    if (server?.listening) await new Promise<void>((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
    if (screenshotDirectory && screenshots.length) fs.writeFileSync(path.join(screenshotDirectory, `manifest-${browserName}.json`), JSON.stringify({
      schemaVersion: 1, browser: browserName, browserVersion: runtimeVersion,
      measurementBrowser: PINNED_GRAPH_BROWSER_VERSION, screenshots,
    }, null, 2) + "\n");
  });

  async function capture(page: Page, state: string, selector?: string): Promise<void> {
    if (!screenshotDirectory) return;
    fs.mkdirSync(screenshotDirectory, { recursive: true });
    if (await page.evaluate(() => document.documentElement.classList.contains("graphs-interactive"))) await animationFrame(page);
    const file = `${browserName}-${state}.png`, output = path.join(screenshotDirectory, file);
    if (selector) await page.locator(selector).screenshot({ path: output, animations: "disabled", caret: "hide" });
    else await page.screenshot({ path: output, animations: "disabled", caret: "hide" });
    screenshots.push({ state, file, viewport: page.viewportSize(), layoutDigests: await page.locator("svg.prepared-graph").evaluateAll((graphs) =>
      graphs.map((graph) => graph.getAttribute("data-layout-digest")!).sort()) });
  }

  async function visit(url: string, action: (page: Page, audit: Audit) => Promise<void>, options: BrowserContextOptions & { local?: boolean; deferFonts?: boolean } = {}): Promise<void> {
    const { local, deferFonts, ...browserOptions } = options;
    const context = await browser.newContext({ viewport: { width: 1920, height: 1200 }, locale: "en-US", timezoneId: "UTC", ...browserOptions });
    contexts.add(context);
    let releaseFonts = () => {};
    const fontsReleased = new Promise<void>((resolve) => { releaseFonts = resolve; });
    if (!deferFonts) releaseFonts();
    const requestStart = serverRequests.length;
    const audit: Audit = { requests: [], errors: [], releaseFonts, serverRequests: () => serverRequests.slice(requestStart) };
    context.on("request", (request) => audit.requests.push(request.url()));
    // Account/comment services are unrelated to graph rendering. Stub them so
    // the test cannot call external services or depend on a signed-in account.
    await context.route("**/*", async (route) => {
      const request = route.request(), target = new URL(request.url());
      if (target.protocol !== "file:" && target.origin !== origin) {
        const headers = { "Access-Control-Allow-Origin": request.headers().origin ?? origin,
          "Access-Control-Allow-Credentials": "true", "Access-Control-Allow-Headers": "*" };
        await route.fulfill({ status: 200, headers, contentType: request.resourceType() === "script" ? "text/javascript" : "application/json",
          body: request.resourceType() === "script" ? "" : "{}" });
      } else {
        if (target.pathname.endsWith(".woff2")) await fontsReleased;
        await route.continue();
      }
    });
    await context.addInitScript(({ local }) => {
      const state = { computation: { workers: 0, legacy: 0, textMeasurements: 0 }, violations: [] as string[] };
      (window as any).__graphAudit = state;
      document.addEventListener("securitypolicyviolation", (event) => state.violations.push(`${event.effectiveDirective}: ${event.blockedURI}`));
      if (!local) {
        Object.defineProperty(window, "laxLayout", { configurable: true,
          get() { state.computation.legacy++; throw new Error("A public view attempted browser layout"); },
          set() { state.computation.legacy++; throw new Error("A public view loaded browser layout"); } });
        const NativeWorker = window.Worker;
        window.Worker = class extends NativeWorker {
          constructor(url: string | URL, options?: WorkerOptions) { state.computation.workers++; super(url, options); throw new Error("A public graph started a worker"); }
        };
        for (const [prototype, name] of [[SVGGraphicsElement.prototype, "getBBox"], [SVGTextContentElement.prototype, "getComputedTextLength"]] as const) {
          const original = (prototype as any)[name];
          (prototype as any)[name] = function (...args: unknown[]) {
            if (this.closest("svg.prepared-graph")) state.computation.textMeasurements++;
            return original.apply(this, args);
          };
        }
      }
    }, { local: Boolean(local) });
    const page = await context.newPage();
    page.on("pageerror", (error) => audit.errors.push(error.message));
    try {
      await page.goto(url, { waitUntil: deferFonts ? "domcontentloaded" : "load" });
      if (browserOptions.javaScriptEnabled !== false) await page.waitForFunction(() => document.documentElement.classList.contains("graphs-interactive"));
      if (browserOptions.javaScriptEnabled !== false) await animationFrame(page);
      await action(page, audit);
      expect(await page.evaluate(() => (window as any).__graphAudit?.violations ?? [])).toEqual([]);
      expect(audit.errors).toEqual([]);
    } finally { releaseFonts(); await context.close(); contexts.delete(context); }
  }
  const url = (relative = mainPage, site = "archive") => `${origin}/preview/graph-drawing/${site}/${relative}`;

  it("contains actual multiline and large-ordinal ink in the serialized SVG at measured baselines", async () => {
    const display = dockInkFixture(), requests = displayLabelRequests([display]);
    const measurer = createGraphMeasurer({ executablePath: executable });
    let metrics;
    try { metrics = await measurer.measureLabels(requests); } finally { await measurer.close(); }
    const measured = measureDisplayGraph(display, new Map(requests.map((request, i) => [request.text, metrics[i]!])));
    const result = layoutGraph(measured.graph, { inputDigest: "measured-large-ordinal" });
    const svg = graphSvg(measured, result.geometry, "large-ordinal");
    const expected = [...measured.drawings].flatMap(([id, drawing]) => [
      { id, bounds: drawing.body, lines: drawing.lines },
      ...drawing.docks.map((dock) => ({ id: dock.id, bounds: dock.bounds, lines: dock.lines })),
    ]).filter((entry) => entry.lines.length);
    expect(measured.drawings.get("c:Claims")!.lines.length).toBeGreaterThan(1);
    expect(svg).not.toContain('dominant-baseline="central"');
    const context = await browser.newContext({ javaScriptEnabled: false });
    try {
      await context.route("**/*", async (route) => {
        const relative = new URL(route.request().url()).pathname.slice(1);
        if (!relative) await route.fulfill({ contentType: "text/html", body:
          '<!doctype html><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; style-src \'self\'; font-src \'self\'"><link rel="stylesheet" href="style.css"><body>' + svg + "</body>" });
        else if (relative === "style.css" || measurer.environment.fontFaces.some((face) => face.file === relative))
          await route.fulfill({ contentType: relative.endsWith(".css") ? "text/css" : "font/woff2", body: fs.readFileSync(siteAssetPath(relative)) });
        else await route.abort();
      });
      const page = await context.newPage();
      await page.goto("https://graph-docks.test/");
      await expect.poll(() => page.evaluate(() => document.fonts.status)).toBe("loaded");
      const actual = await page.locator("svg [data-node-id]").evaluateAll((elements) => elements.flatMap((node) => {
        const text = node.querySelector(".graph-label, .graph-dock-number");
        if (!text) return [];
        const ink = (text as SVGGraphicsElement).getBBox(), shape = node.querySelector("rect, circle") as SVGGraphicsElement;
        const { x, y, width, height } = shape.getBBox();
        const circle = shape.tagName === "circle", radius = width / 2;
        return [{ id: node.getAttribute("data-node-id"), label: text.textContent, href: node.getAttribute("href"), width,
          contained: ink.x >= x && ink.y >= y && ink.x + ink.width <= x + width && ink.y + ink.height <= y + height &&
            (!circle || [ink.x, ink.x + ink.width].every((a) => [ink.y, ink.y + ink.height].every((b) => Math.hypot(a - x - radius, b - y - radius) <= radius))),
          inkWidth: ink.width, lines: [...text.querySelectorAll("tspan")].map((span) => {
            const ink = (span as SVGGraphicsElement).getBBox();
            return { text: span.textContent, x: Number(span.getAttribute("x")), y: Number(span.getAttribute("y")),
              ink: { x: ink.x, y: ink.y, width: ink.width, height: ink.height } };
          }) }];
      }));
      expect(actual).toHaveLength(expected.length);
      expect(actual.every((entry) => entry.contained)).toBe(true);
      for (const entry of actual) {
        const reference = expected.find((value) => value.id === entry.id)!;
        expect(entry.lines).toHaveLength(reference.lines.length);
        entry.lines.forEach((line, i) => {
          if (!entry.id!.startsWith("dock:"))
            expect(line.ink.x + line.ink.width / 2).toBeCloseTo(reference.bounds.x + reference.bounds.width / 2, 1);
          expect(line.text).toBe(reference.lines[i]!.text);
          expect(line.x).toBe(reference.lines[i]!.x); expect(line.y).toBe(reference.lines[i]!.y);
          // Only the pinned measurement engine promises identical glyph boxes.
          // Other engines consume the same baselines and must fit their actual
          // ink inside the unchanged published capsule.
          if (browserName === "chromium") for (const key of ["x", "y", "width", "height"] as const)
            expect(line.ink[key], `${entry.id}, line ${i}, ${JSON.stringify(line.text)}, ink.${key}; actual=${JSON.stringify(line.ink)}; measured=${JSON.stringify(reference.lines[i]!.ink)}`)
              .toBeCloseTo(reference.lines[i]!.ink[key], 2);
        });
      }
      const large = actual.find((entry) => entry.id === "dock:Claims.last")!;
      expect(large).toMatchObject({ label: "9876543210", href: "claims.html#last" });
      expect(large.inkWidth).toBeGreaterThan(18);
      const numeral = metrics[requests.findIndex((request) => request.text === "9876543210")]!;
      expect(large.width).toBeGreaterThanOrEqual(numeral.width + 8);
      const first = actual.find((entry) => entry.id === "dock:Claims.first")!;
      const firstNumeral = metrics[requests.findIndex((request) => request.text === "1")]!;
      expect(first.width).toBeGreaterThanOrEqual(18);
      expect(first.width).toBeGreaterThanOrEqual(firstNumeral.width + 8);
      const source = measured.graph.nodes.find((node) => node.id === "c:Claims")!;
      for (const dock of measured.drawings.get(source.id)!.docks) {
        const port = source.ports.find((value) => value.semanticEndpointId === dock.statementId)!;
        expect(port.mode).toBe("fixed-position");
        expect(port.offset!.x).toBeCloseTo(dock.bounds.x + dock.bounds.width / 2, 2);
        expect(port.offset!.y).toBeCloseTo(dock.bounds.y, 2);
        expect(source.labelBoxes).toContainEqual(dock.lines[0]!.ink);
      }
    } finally { await context.close(); }
  }, 30_000);

  it("publishes every default graph as an accessible SVG with working links and no JavaScript", async () => {
    expect(archiveReport.localFallback).toBe(false);
    expect(archiveReport.statistics.measurement?.browserLaunches).toBe(1);
    expect(fs.existsSync(path.join(archive, "assets", "layout.js"))).toBe(false);
    expect(fs.existsSync(path.join(archive, "assets", "graph-local"))).toBe(false);
    await visit(url(), async (page, audit) => {
      expect(await page.locator("svg.prepared-graph").count()).toBe(3);
      await openConcepts(page);
      for (const id of ["concept-dag", "proof-network", "submission-dag"]) {
        expect(await page.locator(`#${id} svg`).isVisible()).toBe(true);
        expect(await page.locator(`#${id} svg a[href]`).count()).toBeGreaterThan(0);
      }
      expect(await page.locator("#proof-network .net-proof").count()).toBe(9);
      expect(await page.locator("#proof-network .net-dock").count()).toBe(2);
      expect(await page.locator("#proof-network [data-edge-id]").evaluateAll((edges) => new Set(edges.map((e) => e.getAttribute("data-edge-id"))).size)).toBe(21);
      expect(await page.locator(".proof-network-figure [data-graph-expand]").isVisible()).toBe(false);
      await capture(page, "no-javascript", ".proof-network-figure");
      const href = await page.locator('#proof-network [data-node-id="dock:Lax701.Base.s2"]').getAttribute("href");
      expect(new URL(href!, page.url()).pathname).toBe("/preview/graph-drawing/archive/Lax701/Lax701.Base.html");
      await page.locator('#proof-network [data-node-id="dock:Lax701.Base.s2"]').click();
      expect(page.url()).toContain("/preview/graph-drawing/archive/Lax701/Lax701.Base.html#s-Lax701.Base.s2");
      expect(audit.requests.filter((value) => /graph-(?:local|interaction)/u.test(value))).toEqual([]);
    }, { javaScriptEnabled: false });
  }, 30_000);

  it("switches all four precomputed ancestry views, including lazy files, under a preview prefix", async () => {
    await visit(url(), async (page, audit) => {
      await openConcepts(page);
      const initial = await fingerprint(page, "concept-dag");
      const ids = () => page.locator("#concept-dag [data-node-id]").evaluateAll((nodes) => nodes.map((node) => node.getAttribute("data-node-id")).sort());
      const core = fixture()[1]!.output!.concepts.map((concept) => `c:${concept.id}`).sort();
      expect(await ids()).toEqual([...core, "c:Lax701.Base"].sort());
      expect(audit.requests.filter((value) => value.includes("/graph-views/"))).toHaveLength(0);
      await page.locator("#concept-expand").click();
      await page.waitForFunction(() => document.querySelector("#concept-expand")?.getAttribute("aria-pressed") === "false");
      expect(await ids()).toEqual(core);
      await page.locator("#concept-descend").click();
      await page.waitForFunction(() => document.querySelector("#concept-descend")?.getAttribute("aria-pressed") === "true");
      expect(await ids()).toEqual([...core, "c:Lax703.Application"].sort());
      await page.locator("#concept-expand").click();
      await page.waitForFunction(() => document.querySelector("#concept-expand")?.getAttribute("aria-pressed") === "true");
      expect(await ids()).toEqual([...core, "c:Lax701.Base", "c:Lax703.Application"].sort());
      // The direct Base -> Main import remains visible alongside its long path.
      expect(await page.locator('#concept-dag [data-edge-id*="Lax701.Base->Lax702.Main"]').count()).toBe(1);
      await capture(page, "ancestry-all", "details:has(#concept-dag) .graph-figure");
      await page.locator("#concept-descend").click();
      await page.waitForFunction(() => document.querySelector("#concept-descend")?.getAttribute("aria-pressed") === "false");
      expect(await fingerprint(page, "concept-dag")).toEqual(initial);
      const lazy = audit.requests.filter((value) => value.includes("/graph-views/"));
      expect(lazy).toHaveLength(3);
      expect(lazy.every((value) => value.startsWith(`${origin}/preview/graph-drawing/archive/assets/graph-views/`))).toBe(true);
      await expectNoPublicLayout(page, audit);
    });
  }, 30_000);

  it("keeps geometry and the SVG element during camera, fullscreen, resize and keyboard interaction", async () => {
    await visit(url(), async (page, audit) => {
      const figure = page.locator(".proof-network-figure"), container = page.locator("#proof-network");
      await container.scrollIntoViewIfNeeded();
      const original = await fingerprint(page);
      await container.evaluate((element) => { (window as any).__initialGraphSvg = element.querySelector("svg"); });
      const viewport = await container.evaluate((element) => ({ top: element.scrollTop, left: element.scrollLeft,
        middle: (element.scrollWidth - element.clientWidth) / 2, overflow: element.scrollWidth > element.clientWidth }));
      expect(viewport.top).toBe(0);
      if (viewport.overflow) expect(Math.abs(viewport.left - viewport.middle)).toBeLessThanOrEqual(1);
      else expect(viewport.left).toBe(0);
      await capture(page, "default", ".proof-network-figure");
      await figure.locator('[data-graph-zoom="in"]').click(); await animationFrame(page);
      expect(await figure.locator("[data-graph-zoom-status]").textContent()).toBe("120%");
      await capture(page, "zoom-120", ".proof-network-figure");
      await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
      expect(await figure.getAttribute("role")).toBe("dialog");
      expect(await figure.getAttribute("aria-modal")).toBe("true");
      await capture(page, "fullscreen-auto-fit");
      await page.setViewportSize({ width: 1100, height: 850 }); await animationFrame(page);
      expect(await fingerprint(page)).toEqual(original);
      expect(await container.evaluate((element) => element.querySelector("svg") === (window as any).__initialGraphSvg)).toBe(true);
      await capture(page, "fullscreen-resized");
      await page.keyboard.press("Escape");
      await animationFrame(page);
      expect(await figure.locator("[data-graph-zoom-status]").textContent()).toBe("120%");
      expect(await figure.getAttribute("aria-modal")).toBeNull();
      expect(await figure.locator("[data-graph-expand]").evaluate((element) => document.activeElement === element)).toBe(true);
      await figure.locator('[data-graph-zoom="reset"]').click(); await animationFrame(page);
      // Zooming out must not retain scrollbars merely because the root SVG
      // still has its original, larger dimensions.
      for (let i = 0; i < 9; i++) await figure.locator('[data-graph-zoom="out"]').click();
      await animationFrame(page);
      expect(await container.evaluate((el) => ({ x: getComputedStyle(el).overflowX, y: getComputedStyle(el).overflowY })))
        .toEqual({ x: "hidden", y: "hidden" });
      await figure.locator('[data-graph-zoom="reset"]').click(); await animationFrame(page);
      const node = page.locator(`#proof-network [data-node-id="${proofId}"]`);
      await node.focus(); await page.keyboard.press("+"); await animationFrame(page);
      expect(await figure.locator("[data-graph-zoom-status]").textContent()).toBe("120%");
      await page.keyboard.press("0"); await animationFrame(page);
      expect(await figure.locator("[data-graph-zoom-status]").textContent()).toBe("100%");
      expect(await fingerprint(page)).toEqual(original);
      await expectNoPublicLayout(page, audit);
    });
  }, 30_000);

  it("gives inline graphs only the scrollbars they need, including native scrollbar space", async () => {
    await visit(url("Lax701/index.html"), async (page) => {
      const container = page.locator("#submission-dag");
      const dimensions = () => container.evaluate((el) => ({
        x: getComputedStyle(el).overflowX, y: getComputedStyle(el).overflowY,
        width: el.clientWidth, height: el.clientHeight, scrollWidth: el.scrollWidth, scrollHeight: el.scrollHeight,
        horizontalBar: (el as HTMLElement).offsetHeight - el.clientHeight,
      }));
      expect(await dimensions()).toMatchObject({ x: "hidden", y: "hidden" });
      const drawingWidth = await container.locator("svg").evaluate((el) => el.getBoundingClientRect().width);
      await page.setViewportSize({ width: Math.floor(drawingWidth), height: 850 }); await animationFrame(page);
      const narrow = await dimensions();
      expect(narrow.scrollWidth).toBeGreaterThan(narrow.width);
      expect(narrow.x).toBe("auto");
      expect(narrow.y).toBe("hidden");
      expect(narrow.scrollHeight).toBeLessThanOrEqual(narrow.height + 1);
      if (browserName === "chromium") expect(narrow.horizontalBar).toBeGreaterThan(0);
      await page.setViewportSize({ width: 1920, height: 1200 }); await animationFrame(page);
      expect(await dimensions()).toMatchObject({ x: "hidden", y: "hidden" });
    });
  }, 30_000);

  it("keeps vertically fitting graphs clear of both banners during dragging, zoom and resize", async () => {
    await visit(url("Lax701/index.html"), async (page) => {
      await openConcepts(page);
      for (const id of ["concept-dag", "submission-dag", "proof-network"]) {
        const container = page.locator(`#${id}`), figure = container.locator("xpath=..");
        const original = await fingerprint(page, id);
        const contained = async () => {
          const result = await container.evaluate((el) => {
            const box = el.getBoundingClientRect(), top = box.top + el.clientTop, bottom = top + el.clientHeight;
            return { overflow: getComputedStyle(el).overflowY, scroll: el.scrollTop,
              inside: [...el.querySelectorAll('[data-node-id]')].every((node) => {
                const rect = node.getBoundingClientRect();
                return rect.top >= top - 1 && rect.bottom <= bottom + 1;
              }) };
          });
          expect(result).toEqual({ overflow: "hidden", scroll: 0, inside: true });
        };
        for (const expanded of [false, true]) {
          if (expanded) await figure.locator('[data-graph-expand]').click();
          for (let i = 0; i < 4; i++) await figure.locator('[data-graph-zoom="out"]').click();
          await container.scrollIntoViewIfNeeded(); await animationFrame(page);
          await contained();
          for (const dy of [-1500, 1500]) {
            const plot = (await container.boundingBox())!, svg = (await container.locator('svg').boundingBox())!;
            const x = Math.max(plot.x, svg.x) + 2, y = Math.max(plot.y, svg.y) + 2;
            await page.mouse.move(x, y); await page.mouse.down();
            await page.mouse.move(x, y + dy, { steps: 4 }); await page.mouse.up();
            await animationFrame(page); await contained();
          }
          // Native focus/scroll offsets must not conceal an otherwise fitting drawing.
          await container.evaluate((el) => { el.scrollTop = 100; });
          await animationFrame(page); await contained();
          await page.setViewportSize({ width: 1600, height: 900 }); await animationFrame(page);
          await contained();
          if (expanded) { await page.keyboard.press('Escape'); await animationFrame(page); }
        }
        expect(await fingerprint(page, id)).toEqual(original);
      }
    });
  }, 30_000);

  it("centers readable expanded graphs, caps enlargement, and preserves manual zoom until reset", async () => {
    await visit(url("Lax701/index.html"), async (page) => {
      await openConcepts(page);
      for (const id of ["concept-dag", "submission-dag", "proof-network"]) {
        const container = page.locator(`#${id}`), figure = container.locator("xpath=..");
        await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
        const framed = await container.evaluate((el) => {
          const svg = el.querySelector("svg")!, camera = svg.querySelector("[data-graph-camera]") as SVGGraphicsElement;
          const bounds = svg.viewBox.baseVal, matrix = camera.getScreenCTM()!, box = el.getBoundingClientRect();
          const origin = new DOMPoint(bounds.x, bounds.y).matrixTransform(matrix);
          return { scale: matrix.a, desired: Math.max(1, Math.min(1.5, (el.clientWidth - 32) / bounds.width, (el.clientHeight - 32) / bounds.height)),
            dx: origin.x + bounds.width * matrix.a / 2 - box.left - el.clientLeft - el.clientWidth / 2,
            dy: origin.y + bounds.height * matrix.d / 2 - box.top - el.clientTop - el.clientHeight / 2 };
        });
        expect(framed.scale).toBeCloseTo(framed.desired, 6);
        expect(Math.abs(framed.dx)).toBeLessThan(1);
        expect(Math.abs(framed.dy)).toBeLessThan(1);
        await figure.locator('[data-graph-zoom="in"]').click(); await animationFrame(page);
        const manual = await figure.locator("[data-graph-zoom-status]").textContent();
        await page.setViewportSize({ width: 1700, height: 1100 }); await animationFrame(page);
        expect(await figure.locator("[data-graph-zoom-status]").textContent()).toBe(manual);
        await figure.locator('[data-graph-zoom="reset"]').click(); await animationFrame(page);
        expect(Number((await figure.locator("[data-graph-zoom-status]").textContent())!.replace("%", ""))).toBeLessThanOrEqual(150);
        await page.keyboard.press("Escape"); await animationFrame(page);
      }
    });
  }, 30_000);

  it("keeps panned maps visible beyond their original SVG bounds and uses one shared banner", async () => {
    await visit(url("Lax701/index.html"), async (page) => {
      await openConcepts(page);
      for (const [id, directions] of [["concept-dag", [[0, 180]]], ["submission-dag", [[250, 0], [-250, 0]]]] as const) {
        const container = page.locator(`#${id}`), figure = container.locator("xpath=..");
        expect(await figure.locator(":scope > .graph-controls").count()).toBe(1);
        expect(await figure.locator(".graph-toolbar").count()).toBe(0);
        expect(await figure.locator(".graph-controls").evaluate((el) => getComputedStyle(el).backgroundColor)).toBe("rgb(250, 249, 247)");
        await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
        const svg = container.locator("svg.prepared-graph"), node = svg.locator("[data-node-id]").first();
        for (const [dx, dy] of directions) {
          await figure.locator('[data-graph-zoom="reset"]').click(); await animationFrame(page);
          const box = (await svg.boundingBox())!;
          await page.mouse.move(box.x + 2, box.y + 2);
          await page.mouse.down();
          await page.mouse.move(box.x + 2 + dx, box.y + 2 + dy, { steps: 4 });
          await page.mouse.up(); await animationFrame(page);
          const visible = await node.evaluate((el) => {
            const box = el.getBoundingClientRect();
            return el.contains(document.elementFromPoint(box.left + box.width / 2, box.top + box.height / 2));
          });
          expect(visible).toBe(true);
        }
        await node.focus(); await animationFrame(page);
        const tooltip = figure.locator(".graph-tooltip");
        expect(await tooltip.evaluate((el) => getComputedStyle(el).fontWeight)).toBe("400");
        expect(await tooltip.locator("strong").first().evaluate((el) => getComputedStyle(el).fontWeight)).toBe("700");
        expect(await tooltip.evaluate((el) => getComputedStyle(el).backgroundColor)).toBe("rgb(255, 255, 255)");
        await page.keyboard.press("Escape"); await animationFrame(page);
      }
    });
  }, 30_000);

  it("keeps math tooltips legible and outside the normal proof window on hover and keyboard focus", async () => {
    await visit(url(), async (page, audit) => {
      const figure = page.locator(".proof-network-figure"), tooltip = figure.locator(".graph-tooltip");
      const dock = page.locator('#proof-network [data-node-id="dock:Lax701.Base.s2"]');
      await dock.scrollIntoViewIfNeeded(); await dock.focus(); await animationFrame(page);
      expect(await tooltip.textContent()).toBe("Lax701.Base.s2");
      expect(await dock.locator("title").count()).toBe(0);
      const node = page.locator(`#proof-network [data-node-id="${proofId}"]`);
      await node.scrollIntoViewIfNeeded(); await node.focus(); await animationFrame(page);
      expect(await tooltip.isVisible()).toBe(true);
      expect(await tooltip.locator(".katex").count()).toBe(2);
      expect(await tooltip.locator(".katex-display").count()).toBe(1);
      expect(await tooltip.textContent()).not.toMatch(/(?:Title|Description):|click to open/u);
      expect(await page.locator("#proof-network .hot").count()).toBe(2);
      const normal = await tooltip.evaluate((element) => {
        const style = getComputedStyle(element), box = element.getBoundingClientRect(), figure = element.closest("figure")!.getBoundingClientRect();
        return { fontWeight: style.fontWeight, background: style.backgroundColor, opacity: style.opacity, placement: (element as HTMLElement).dataset.placement,
          outside: box.right <= figure.left || box.left >= figure.right, centerY: (box.top + box.bottom) / 2,
          left: box.left, top: box.top,
          mathWeight: getComputedStyle(element.querySelector(".katex")!).fontWeight };
      });
      expect(normal).toMatchObject({ fontWeight: "700", mathWeight: "700", opacity: "1", background: "rgb(255, 255, 255)", outside: true });
      expect(["left", "right"]).toContain(normal.placement);
      const anchor = await node.boundingBox();
      expect(Math.abs(normal.centerY - (anchor!.y + anchor!.height / 2))).toBeLessThanOrEqual(1);
      await capture(page, "math-tooltip-normal");
      // Resize while keyboard focus stays on the node. A fixed-position panel
      // must follow the new viewport, or hide if its node leaves the window.
      await page.setViewportSize({ width: 1600, height: 1200 }); await animationFrame(page);
      const resized = await tooltip.evaluate((element) => {
        const box = element.getBoundingClientRect();
        return { hidden: (element as HTMLElement).hidden, left: box.left, top: box.top, right: box.right };
      });
      if (!resized.hidden) {
        expect(Math.abs(resized.left - normal.left) + Math.abs(resized.top - normal.top)).toBeGreaterThan(0.1);
        expect(resized.left).toBeGreaterThanOrEqual(0);
        expect(resized.right).toBeLessThanOrEqual(1600);
      }
      await capture(page, "math-tooltip-resized");
      await page.setViewportSize({ width: 1920, height: 1200 }); await animationFrame(page);
      await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
      await node.hover(); await animationFrame(page);
      expect(await tooltip.isHidden()).toBe(true);
      expect(await page.locator('.prepared-graph title, .prepared-graph [title]').count()).toBe(0);
      await node.focus(); await animationFrame(page);
      expect(await tooltip.isVisible()).toBe(true);
      expect(await tooltip.evaluate((element) => getComputedStyle(element).backgroundColor)).toBe("rgb(255, 255, 255)");
      const appearance = () => tooltip.evaluate((element) => {
        const box = element.getBoundingClientRect(), style = getComputedStyle(element), pixels = window.devicePixelRatio;
        return { size: style.fontSize, width: box.width, height: box.height,
          x: box.left * pixels, y: box.top * pixels };
      });
      const originalPanel = await appearance();
      for (const key of ["-", "+"]) {
        await page.keyboard.press(key); await animationFrame(page);
        const panel = await appearance();
        expect(panel.size).toBe(originalPanel.size);
        expect(panel.width).toBeCloseTo(originalPanel.width, 1);
        expect(panel.height).toBeCloseTo(originalPanel.height, 1);
        expect(Math.abs(panel.x - Math.round(panel.x))).toBeLessThan(0.02);
        expect(Math.abs(panel.y - Math.round(panel.y))).toBeLessThan(0.02);
      }
      await expectNoPublicLayout(page, audit);
      await expectLabelContainment(page);
    });
  }, 30_000);

  it("opens the large proof view from nodes and links, then clears the focused chain", async () => {
    await visit(url(), async (page, audit) => {
      const figure = page.locator(".proof-network-figure"), container = page.locator("#proof-network");
      const proof = container.locator(`[data-node-id="${proofId}"]`);
      expect(await figure.locator(".graph-detail-panel").count()).toBe(0);
      expect(await proof.getAttribute("href")).toBeTruthy();

      const pageUrl = page.url();
      const initialScale = Number((await figure.locator("[data-graph-zoom-status]").textContent())!.replace("%", ""));
      await proof.click();
      expect(await figure.getAttribute("class")).toContain("graph-expanded");
      expect(page.url()).toBe(pageUrl);
      const panel = figure.locator(".graph-detail-panel");
      expect(await panel.isVisible()).toBe(true);
      expect(await panel.locator("h3").first().textContent()).toBe("Proof of Main χ result");
      expect(await panel.textContent()).toContain("1 open assumption");
      expect(await panel.textContent()).toContain("Checked relationship");
      const submissionName = panel.locator(".graph-detail-facts dd").first();
      expect(await submissionName.locator(".katex").count()).toBe(1);
      expect(await submissionName.textContent()).not.toContain("$");
      const relationship = panel.locator(".graph-detail-claims");
      expect(await relationship.locator(".katex").count()).toBe(1);
      expect(await relationship.innerText()).not.toContain("$");
      expect(await panel.locator(".graph-detail-action").getAttribute("href")).toBeTruthy();
      const placement = await panel.evaluate((element) => {
        const panel = element.getBoundingClientRect(), figure = element.parentElement!.getBoundingClientRect();
        const controls = element.parentElement!.querySelector(".graph-controls")!.getBoundingClientRect();
        return { rightGap: figure.right - panel.right, onRight: panel.left > (figure.left + figure.right) / 2,
          topGap: panel.top - controls.bottom, heightRatio: panel.height / figure.height,
          overflow: getComputedStyle(element.querySelector(".graph-detail-scroll")!).overflowY };
      });
      expect(placement.rightGap).toBeLessThan(10);
      expect(placement.onRight).toBe(true);
      expect(placement.topGap).toBeGreaterThanOrEqual(4);
      expect(placement.topGap).toBeLessThanOrEqual(8);
      expect(placement.heightRatio).toBeLessThanOrEqual(0.83);
      expect(placement.overflow).toBe("auto");
      expect(await container.locator(".graph-selected").count()).toBe(1);
      expect(await container.locator(".graph-related").count()).toBeGreaterThan(0);
      expect(await container.locator(".graph-dimmed").count()).toBeGreaterThan(0);
      await page.waitForTimeout(1_000); await animationFrame(page);
      const focusedScale = Number((await figure.locator("[data-graph-zoom-status]").textContent())!.replace("%", ""));
      expect(focusedScale).toBeGreaterThan(initialScale);
      await capture(page, "proof-detail-proof");

      const concept = container.locator('[data-node-id="s:Lax702.Main.s1"]');
      await concept.click(); await page.waitForTimeout(1_000); await animationFrame(page);
      expect(await panel.locator("h3").first().textContent()).toBe("Main χ result");
      expect(await panel.textContent()).toContain("Natural-language statement");
      expect(await panel.textContent()).toContain("Lean formalization");
      const leanPreview = panel.locator(".graph-detail-formalization-preview");
      expect(await leanPreview.locator("pre code").textContent()).toContain("s1 : True");
      expect(await leanPreview.getAttribute("href")).toContain("Lax702.Main.html#s-Lax702.Main.s1");
      const formalizationWidth = await leanPreview.evaluate((element) => ({
        own: element.getBoundingClientRect().width,
        parent: element.parentElement!.getBoundingClientRect().width,
        overflow: getComputedStyle(element).overflow,
        preOverflow: getComputedStyle(element.querySelector("pre")!).overflow,
        whiteSpace: getComputedStyle(element.querySelector("pre")!).whiteSpace,
      }));
      expect(formalizationWidth.own / formalizationWidth.parent).toBeGreaterThan(0.95);
      expect(formalizationWidth.overflow).toBe("hidden");
      expect(formalizationWidth.preOverflow).toBe("hidden");
      expect(formalizationWidth.whiteSpace).toBe("pre-wrap");
      await capture(page, "proof-detail-concept");

      await container.evaluate((element) => element.dispatchEvent(new MouseEvent("click", { bubbles: true })));
      await animationFrame(page);
      expect(await panel.isHidden()).toBe(true);
      expect(await container.locator(".graph-selected, .graph-related, .graph-dimmed").count()).toBe(0);
      const restoredScale = Number((await figure.locator("[data-graph-zoom-status]").textContent())!.replace("%", ""));
      expect(focusedScale / restoredScale).toBeGreaterThanOrEqual(1.19);
      expect(focusedScale / restoredScale).toBeLessThanOrEqual(1.21);

      await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
      const edge = container.locator('[data-edge-hit][aria-label*="Main χ result"]').first();
      expect(await edge.evaluate((element) => getComputedStyle(element).pointerEvents)).toBe("stroke");
      await edge.click({ force: true });
      await animationFrame(page);
      expect(await figure.getAttribute("class")).toContain("graph-expanded");
      expect(await panel.textContent()).toMatch(/(?:used as an assumption|establishes)/u);
      expect(await container.locator("[data-edge-id].graph-selected").count()).toBeGreaterThan(0);
      await expectNoPublicLayout(page, audit);

      await concept.click(); await animationFrame(page);
      const fullSource = panel.locator(".graph-detail-formalization-preview");
      await Promise.all([
        page.waitForURL(/Lax702\.Main\.html#s-Lax702\.Main\.s1$/u),
        fullSource.click(),
      ]);
      const sourcePosition = await page.locator('[id="s-Lax702.Main.s1"]').evaluate((anchor) => ({
        top: anchor.getBoundingClientRect().top,
        middle: window.innerHeight / 2,
      }));
      expect(sourcePosition.top).toBeCloseTo(sourcePosition.middle, 0);
    });
  }, 45_000);

  it("reserves graph dimensions while fonts are delayed without running browser layout", async () => {
    await visit(url(), async (page, audit) => {
      expect(await page.evaluate(() => document.fonts.status)).toBe("loading");
      const dimensions = () => page.locator(".figure-container").evaluateAll((elements) => elements.map((element) => {
        const rect = element.getBoundingClientRect();
        return { id: element.id, width: rect.width, height: rect.height };
      }));
      const before = await dimensions(), geometry = await fingerprint(page);
      audit.releaseFonts(); await page.evaluate(() => document.fonts.ready); await animationFrame(page);
      expect(await page.evaluate(() => document.fonts.status)).toBe("loaded");
      expect(await dimensions()).toEqual(before);
      expect(await fingerprint(page)).toEqual(geometry);
      await expectNoPublicLayout(page, audit);
      await expectLabelContainment(page);
    }, { deferFonts: true });
  }, 30_000);

  it("remains usable on a narrow reduced-motion touch screen", async () => {
    await visit(url(), async (page, audit) => {
      expect(await page.evaluate(() => matchMedia("(prefers-reduced-motion: reduce)").matches)).toBe(true);
      await openConcepts(page);
      const original = await fingerprint(page), before = await page.locator("#proof-network").boundingBox();
      const figure = page.locator(".proof-network-figure");
      await figure.locator("[data-graph-expand]").click(); await animationFrame(page);
      expect(await page.locator("#proof-network").isVisible()).toBe(true);
      const node = page.locator(`#proof-network [data-node-id="${proofId}"]`);
      await node.focus(); await animationFrame(page);
      const tooltip = await figure.locator(".graph-tooltip").boundingBox();
      expect(tooltip!.x).toBeGreaterThanOrEqual(0);
      expect(tooltip!.x + tooltip!.width).toBeLessThanOrEqual(390);
      await capture(page, "narrow-reduced-motion");
      await page.keyboard.press("Escape"); await animationFrame(page);
      expect(await fingerprint(page)).toEqual(original);
      expect(Math.abs((await page.locator("#proof-network").boundingBox())!.height - before!.height)).toBeLessThan(0.01);
      await expectNoPublicLayout(page, audit);
      await expectLabelContainment(page);
    }, { viewport: { width: 390, height: 844 }, reducedMotion: "reduce",
      // Firefox exposes touch and narrow viewports but not mobile emulation.
      ...(browserName === "firefox" ? {} : { isMobile: true }), hasTouch: true });
  }, 30_000);

  it("switches self-contained file exports without fetching geometry and keeps anonymous graph data filtered", async () => {
    await visit(pathToFileURL(path.join(exported, mainPage)).href, async (page, audit) => {
      await openConcepts(page);
      await page.locator("#concept-descend").click();
      await page.waitForFunction(() => document.querySelector("#concept-descend")?.getAttribute("aria-pressed") === "true");
      expect(await page.locator('#concept-dag [data-node-id="c:Lax703.Application"]').count()).toBe(1);
      await expectNoPublicLayout(page, audit);
      expect(audit.requests.filter((value) => value.includes("/graph-views/"))).toEqual([]);
      await expectLabelContainment(page);
    });
    await visit(url("Lax704/index.html"), async (page, audit) => {
      const raw = await page.locator("#graph-data").textContent();
      expect(raw).not.toMatch(/withheld-browser-source|Withheld Browser Author|withheld-browser-author/u);
      const details = JSON.parse(raw!).proofs.details["proof:Lax704Proofs.Anonymous"];
      expect(details).not.toHaveProperty("leanPath");
      expect(details).not.toHaveProperty("sourceHref");
      expect(await page.locator("#proof-network .net-proof").count()).toBe(1);
      await page.locator("#proof-network .net-proof").focus();
      expect(await page.locator(".proof-network-figure .graph-tooltip").textContent()).not.toMatch(/withheld-browser/u);
      await expectNoPublicLayout(page, audit);
    });
  }, 30_000);

  it("runs the same validated layout in the extracted renderer's local worker without a host Playwright installation", async () => {
    const packaging = path.join(directory, "package-smoke"); fs.mkdirSync(packaging);
    const output = JSON.parse(execFileSync("npm", ["pack", "--ignore-scripts", "--json", "--pack-destination", packaging],
      { cwd: repository, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }));
    const tarball = path.join(packaging, output[0].filename);
    execFileSync("tar", ["-xzf", tarball, "-C", packaging]);
    const unpacked = path.join(packaging, "package"), modules = path.join(unpacked, "node_modules"); fs.mkdirSync(modules);
    // Expose only the declared runtime dependencies. Module resolution from
    // this extracted package cannot reach the repository's Playwright install.
    const manifest = JSON.parse(fs.readFileSync(path.join(unpacked, "package.json"), "utf8"));
    for (const name of Object.keys(manifest.dependencies)) {
      const destination = path.join(modules, name); fs.mkdirSync(path.dirname(destination), { recursive: true });
      fs.symlinkSync(path.join(repository, "node_modules", name), destination, "dir");
    }
    const input = path.join(packaging, "input.json"); fs.writeFileSync(input, JSON.stringify(fixture()));
    const host = path.join(unpacked, "smoke.mjs");
    fs.writeFileSync(host, `import fs from 'node:fs';\nimport {generateSite} from './dist/sitegen/generate.js';\ntry { await import('playwright-core'); throw new Error('Playwright leaked into the isolated host'); } catch(error) { if(error.code !== 'ERR_MODULE_NOT_FOUND') throw error; }\nconst [input, output, cache] = process.argv.slice(2);\nawait generateSite(JSON.parse(fs.readFileSync(input, 'utf8')), output, {graphs: {mode: 'local', cacheDir: cache, measurement: {hostBrowser: false, cacheDir: cache + '/labels'}}, graphReport: report => console.log(JSON.stringify({localFallback: report.localFallback, browserLaunches: report.statistics.measurement?.browserLaunches}))});\n`);
    const environment = { ...process.env }; delete environment.GRAPH_CHROME; delete environment.NODE_PATH;
    const local = path.join(directory, "local");
    const report = JSON.parse(execFileSync(process.execPath, [host, input, local, path.join(packaging, "cache")],
      { cwd: unpacked, env: environment, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }));
    expect(report).toEqual({ localFallback: true, browserLaunches: 0 });
    expect(fs.readFileSync(path.join(local, mainPage), "utf8")).not.toContain('class="prepared-graph"');
    expect(fs.existsSync(path.join(local, "assets", "graph-local", "sitegen", "graph-local-worker.js"))).toBe(true);
    expect(fs.existsSync(path.join(local, "assets", "graph-local", "sitegen", "graph-project.js"))).toBe(false);
    await visit(url(mainPage, "local"), async (page, audit) => {
      await page.waitForFunction(() => document.querySelectorAll(".figure-container svg.prepared-graph").length === 3, undefined, { timeout: 45_000 });
      expect(await page.locator("#proof-network .net-proof").count()).toBe(9);
      expect(await page.locator("#proof-network .net-dock").count()).toBe(2);
      expect(await page.locator("#proof-network [data-edge-id]").evaluateAll((edges) => new Set(edges.map((e) => e.getAttribute("data-edge-id"))).size)).toBe(21);
      await openConcepts(page);
      await page.locator("#concept-descend").click();
      await page.waitForFunction(() => document.querySelector("#concept-descend")?.getAttribute("aria-pressed") === "true");
      expect(await page.locator('#concept-dag [data-node-id="c:Lax703.Application"]').count()).toBe(1);
      expect(await page.locator('.proof-network-figure [data-graph-zoom="in"]').isEnabled()).toBe(true);
      // Firefox does not expose worker imports through Playwright's request
      // events. The local HTTP server independently observes actual transfers.
      const workerModules = audit.serverRequests().filter((value) => value.includes("/graph-local/"));
      expect(workerModules.some((value) => value.endsWith("/sitegen/graph-local-worker.js"))).toBe(true);
      expect(workerModules.some((value) => value.endsWith("/graph-layout/validate.js"))).toBe(true);
      expect(workerModules.filter((value) => /graph-project|graph-measure|markdown|node:|node_modules/u.test(value))).toEqual([]);
      expect(audit.requests.filter((value) => /\/layout\.js|\/dag\.js|elkjs|graphviz|dagre/u.test(value))).toEqual([]);
      await expectLabelContainment(page);
      await capture(page, "local-worker", ".proof-network-figure");
    }, { local: true });
  }, 90_000);
});
