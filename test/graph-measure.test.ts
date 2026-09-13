import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import vm from "node:vm";
import { createHash } from "node:crypto";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { chromium, type Browser } from "playwright-core";
import { siteAssetPath } from "../src/sitegen/assets.js";
import {
  assertGraphGlyphCoverage, createGraphMeasurer, GRAPH_LABEL_FONT_FAMILY,
  graphFontFaceSignature, graphMeasurementEnvironment, graphMeasurementKey, GraphMeasurementUnavailableError,
  normalizeLabelRequest, PINNED_GRAPH_BROWSER_VERSION, validateLabelMetrics,
  type GraphMeasurer, type GraphMeasurementEnvironment, type LabelMetrics,
  type MeasureLabelsProvider, type NormalizedLabelRequest,
} from "../src/sitegen/graph-measure.js";

const environment = graphMeasurementEnvironment("exact-fixture-v1");
const source = fs.readFileSync(siteAssetPath("graph-measure-local.js"), "utf8");
const local = { laxGraphMeasure: undefined as unknown as {
  normalize: typeof normalizeLabelRequest;
  assertCoverage: typeof assertGraphGlyphCoverage;
  keyData: (request: NormalizedLabelRequest, signature: string) => string;
} };
vm.runInNewContext(source, local);

// This is a contract fixture, not an approximate production measurer. Only the
// literal fixture inputs have geometry; other strings fail rather than guess.
const fixtureProvider: MeasureLabelsProvider = async (requests, env) => requests.map((request) => {
  const dimensions = new Map([['Alpha', 31.734375], ['Beta', 24.953125], ['Gamma', 37.859375]]);
  const width = dimensions.get(request.text);
  if (width === undefined) throw new Error("unmeasured fixture label");
  return { text: request.text, width, height: 16,
    signature: graphMeasurementKey(request, env.signature),
    lines: [{ text: request.text, x: 0, y: 12,
      ink: { x: 0, y: 2, width, height: 12 } }] };
});

describe("the graph measurement contract", () => {
  it("uses the same defaults and canonical style key in the local helper", () => {
    for (const input of [
      { text: "Graph classes", maxWidth: 240 },
      { text: "χ and K₃", maxWidth: 160, fontSize: 13, fontWeight: 700 as const, letterSpacing: 0.25, lineHeight: 18 },
    ]) {
      const request = normalizeLabelRequest(input);
      expect(local.laxGraphMeasure.normalize(input)).toEqual(request);
      expect(createHash("sha256").update(local.laxGraphMeasure.keyData(request, environment.signature)).digest("hex"))
        .toBe(graphMeasurementKey(request, environment.signature));
    }
    expect(environment.fontFamily).toBe(GRAPH_LABEL_FONT_FAMILY);
    expect(environment.fontFaceSignature).toBe(graphFontFaceSignature());
    expect(environment.fontFaces).toHaveLength(4);
    expect(Object.isFrozen(environment.fontFaces[0]!.coverage)).toBe(true);
  });

  it("versions font-face context while ignoring unrelated CSS decoration", () => {
    const styles = fs.readFileSync(siteAssetPath("style.css"), "utf8");
    expect(graphFontFaceSignature(styles + "\n.status-open { color: red; }\n")).toBe(environment.fontFaceSignature);
    expect(graphFontFaceSignature(styles.replace("LM-regular.woff2", "LM-other.woff2"))).not.toBe(environment.fontFaceSignature);
  });

  it("diagnoses unsupported glyphs before launching a browser and tests explicit fallbacks", async () => {
    const supported = { text: "χ ε α 𝓕 ⊢ ∈ ◇ K₃ K₅ K₆ café e\u0301", maxWidth: 240 };
    expect(() => assertGraphGlyphCoverage(supported, environment)).not.toThrow();
    expect(() => local.laxGraphMeasure.assertCoverage(supported, environment)).not.toThrow();
    const bad = { text: "A 🧪", maxWidth: 240 };
    expect(() => assertGraphGlyphCoverage(bad, environment)).toThrow(/GRAPH_LABEL_GLYPH_UNSUPPORTED.*U\+1F9EA/u);
    expect(() => local.laxGraphMeasure.assertCoverage(bad, environment)).toThrow(/U\+1F9EA/u);
    const measurer = createGraphMeasurer({ executablePath: "/no/browser/needed" });
    await expect(measurer.measureLabels([bad])).rejects.toThrow(/U\+1F9EA/u);
    expect(measurer.statistics.browserLaunches).toBe(0);
    await measurer.close();
  });

  it("validates actual label characters, baselines and ink bounds independently", async () => {
    const request = normalizeLabelRequest({ text: "Alpha", maxWidth: 240 });
    const metric = (await fixtureProvider([request], environment))[0]!;
    expect(validateLabelMetrics(metric, request, metric.signature)).toBe(true);
    expect(validateLabelMetrics({ ...metric, width: NaN }, request, metric.signature)).toBe(false);
    expect(validateLabelMetrics({ ...metric, lines: [] }, request, metric.signature)).toBe(false);
    expect(validateLabelMetrics({ ...metric, lines: [{ ...metric.lines[0], text: "Alph" }] }, request, metric.signature)).toBe(false);
    expect(validateLabelMetrics({ ...metric, lines: [{ ...metric.lines[0], ink: { x: 0, y: 0, width: 999, height: 12 } }] }, request, metric.signature)).toBe(false);
    for (const input of [{ ...request, maxWidth: Infinity }, { ...request, maxWidth: 0 },
      { ...request, fontSize: -1 }, { ...request, lineHeight: NaN }, { ...request, letterSpacing: -2 }]) {
      expect(() => normalizeLabelRequest(input)).toThrow(/GRAPH_LABEL_REQUEST/u);
      expect(() => local.laxGraphMeasure.normalize(input)).toThrow(/GRAPH_LABEL_REQUEST/u);
    }
  });

  it("deduplicates concurrent requests, batches misses, and makes cold/warm bytes identical", async () => {
    const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), "lax-graph-measure-"));
    const calls: string[][] = [];
    const provider: MeasureLabelsProvider = async (requests, env) => {
      calls.push(requests.map((request) => request.text));
      return fixtureProvider(requests, env);
    };
    const first = createGraphMeasurer({ cacheDir, provider, providerId: "exact-fixture-v1", batchSize: 1 });
    const [cold, other] = await Promise.all([
      first.measureLabels([{ text: "Alpha", maxWidth: 240 }, { text: "Beta", maxWidth: 240 }, { text: "Alpha", maxWidth: 240 }]),
      first.measureLabels([{ text: "Beta", maxWidth: 240 }]),
    ]);
    expect(calls).toEqual([["Alpha"], ["Beta"]]);
    expect(cold[1]).toBe(other[0]);
    expect(cold[0]).toBe(cold[2]);
    expect(Object.isFrozen(cold[0]!.lines[0]!.ink)).toBe(true);
    expect(first.statistics.browserLaunches).toBe(0);
    expect(first.statistics.uniqueLabels).toBe(2);
    await first.close();
    await expect(first.measureLabels([])).rejects.toThrow(/GRAPH_MEASUREMENT_CLOSED/u);
    const second = createGraphMeasurer({ cacheDir, provider: async () => { throw new Error("unexpected cache miss"); }, providerId: "exact-fixture-v1" });
    const warm = await second.measureLabels([{ text: "Alpha", maxWidth: 240 }, { text: "Beta", maxWidth: 240 }, { text: "Alpha", maxWidth: 240 }]);
    expect(JSON.stringify(warm)).toBe(JSON.stringify(cold));
    expect(second.statistics.cacheHits).toBe(3);
    expect(second.statistics.cacheMisses).toBe(0);
    await second.close();
  });

  it("recovers a corrupted cache entry and namespaces each changed style and host version", async () => {
    const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), "lax-graph-measure-corrupt-"));
    const input = { text: "Alpha", maxWidth: 240 };
    const first = createGraphMeasurer({ cacheDir, provider: fixtureProvider, providerId: "exact-fixture-v1" });
    const cold = await first.measureLabels([input]);
    await first.close();
    const file = path.join(cacheDir, `${cold[0]!.signature}.json`);
    const corrupt = JSON.parse(fs.readFileSync(file, "utf8"));
    corrupt.metric.width = 1;
    fs.writeFileSync(file, JSON.stringify(corrupt));
    const second = createGraphMeasurer({ cacheDir, provider: fixtureProvider, providerId: "exact-fixture-v1" });
    expect(await second.measureLabels([input])).toEqual(cold);
    expect(second.statistics.corruptEntries).toBe(1);
    await second.close();
    const signature = cold[0]!.signature;
    for (const changed of [{ ...input, maxWidth: 200 }, { ...input, fontWeight: 700 as const },
      { ...input, fontSize: 13 }, { ...input, letterSpacing: 1 }, { ...input, lineHeight: 17 }]) {
      expect(graphMeasurementKey(changed, environment.signature)).not.toBe(signature);
    }
    expect(graphMeasurementEnvironment("exact-fixture-v2").signature).not.toBe(environment.signature);
  });

  it("distinguishes unavailable tooling from invalid measurements", async () => {
    const missing = createGraphMeasurer({ executablePath: "/not-an-installed-browser/lax" });
    await expect(missing.measureLabels([{ text: "Alpha", maxWidth: 240 }])).rejects.toBeInstanceOf(GraphMeasurementUnavailableError);
    await missing.close();
    const wrong = createGraphMeasurer({ providerId: "broken-fixture-v1", provider: async () => [] });
    await expect(wrong.measureLabels([{ text: "Alpha", maxWidth: 240 }])).rejects.toThrow(/GRAPH_LABEL_RESULT/u);
    await wrong.close();
    expect(() => createGraphMeasurer({ provider: fixtureProvider })).toThrow(/GRAPH_PROVIDER_ID/u);
  });

  it("allows exact cache hits with host browser launches disabled", async () => {
    const cacheDir = fs.mkdtempSync(path.join(os.tmpdir(), "lax-graph-measure-local-"));
    const first = createGraphMeasurer({ cacheDir, provider: fixtureProvider, providerId: "exact-fixture-v1" });
    const request = { text: "Alpha", maxWidth: 240 };
    const expected = await first.measureLabels([request]);
    await first.close();
    const localOnly = createGraphMeasurer({ cacheDir, providerId: "exact-fixture-v1", hostBrowser: false });
    expect(localOnly.environment.signature).toBe(first.environment.signature);
    expect(await localOnly.measureLabels([request])).toEqual(expected);
    await expect(localOnly.measureLabels([{ text: "Gamma", maxWidth: 240 }])).rejects.toBeInstanceOf(GraphMeasurementUnavailableError);
    expect(localOnly.statistics.browserLaunches).toBe(0);
    await localOnly.close();
  });
});

const executable = process.env.GRAPH_CHROME ?? (fs.existsSync("/usr/bin/google-chrome") ? "/usr/bin/google-chrome" : undefined);

describe.skipIf(!executable)("exact graph SVG measurement in the pinned browser", () => {
  let measurer: GraphMeasurer, browser: Browser;
  beforeAll(async () => {
    measurer = createGraphMeasurer({ executablePath: executable, batchSize: 2 });
    browser = await chromium.launch({ executablePath: executable, headless: true,
      args: ["--no-sandbox", "--font-render-hinting=none"] });
    expect(browser.version()).toBe(process.env.GRAPH_CHROME_VERSION ?? PINNED_GRAPH_BROWSER_VERSION);
  }, 30_000);
  afterAll(async () => { await measurer?.close(); await browser?.close(); });

  it("measures proportional glyphs, multiline wrapping, fallback glyphs and a combining cluster", async () => {
    const requests = [
      { text: "WWWW", maxWidth: 240 }, { text: "iiii", maxWidth: 240 },
      { text: "A strong path-of-sets system from treewidth", maxWidth: 90 },
      { text: "χ ε α 𝓕 ⊢ ∈ ◇ K₃ K₅ K₆ café", maxWidth: 240 },
      { text: "oneVeryLongUnbrokenIdentifierEndingHere", maxWidth: 72 },
      { text: "e\u0301e\u0301e\u0301e\u0301", maxWidth: 13 },
      { text: "", maxWidth: 240 }, { text: "first\n\nthird", maxWidth: 240 },
    ];
    const metrics = await measurer.measureLabels(requests);
    expect(metrics[0]!.width).toBeGreaterThan(metrics[1]!.width * 2);
    expect(metrics[2]!.lines.length).toBeGreaterThan(1);
    expect(metrics[4]!.lines.map((line) => line.text).join("")).toBe(requests[4]!.text);
    expect(metrics[5]!.lines.every((line) => /^(?:e\u0301)+$/u.test(line.text))).toBe(true);
    expect(metrics[7]!.lines.map((line) => line.text)).toEqual(["first", "", "third"]);
    metrics.forEach((metric, index) => {
      expect(validateLabelMetrics(metric, requests[index]!, graphMeasurementKey(requests[index]!, measurer.environment.signature))).toBe(true);
      expect(metric.width).toBeLessThanOrEqual(requests[index]!.maxWidth);
      metric.lines.slice(1).forEach((line, i) => expect(line.y - metric.lines[i]!.y).toBeCloseTo(16, 8));
    });
    expect(measurer.statistics.browserLaunches).toBe(1);
    expect(measurer.statistics.batches).toBe(4);
    expect(await measurer.measureLabels(requests)).toEqual(metrics);
  });

  it("reproduces the emitted tspan geometry in an independent SVG and local service", async () => {
    const requests = [
      { text: "A long label for the actual SVG", maxWidth: 92 },
      { text: "K₃ and χ with café", maxWidth: 90, fontWeight: 700 as const, letterSpacing: 0.2 },
    ];
    const metrics = await measurer.measureLabels(requests);
    const context = await browser.newContext();
    try {
      await context.route("**/*", async (route) => {
        const relative = new URL(route.request().url()).pathname.slice(1);
        if (!relative) {
          await route.fulfill({ contentType: "text/html", body: '<!doctype html><meta charset="utf-8"><link rel="stylesheet" href="style.css"><body><script src="graph-measure-local.js"></script></body>' });
        } else if (["graph-measure-local.js", "style.css"].includes(relative) || measurer.environment.fontFaces.some((face) => face.file === relative)) {
          await route.fulfill({ contentType: relative.endsWith(".js") ? "text/javascript" : relative.endsWith(".css") ? "text/css" : "font/woff2", body: fs.readFileSync(siteAssetPath(relative)) });
        } else await route.abort();
      });
      const page = await context.newPage();
      await page.goto("https://graph-local.test/");
      const result = await page.evaluate(async ({ requests: input, metrics: reference, env }) => {
        const measurement = (globalThis as unknown as { laxGraphMeasure: {
          measureLabels(a: typeof input, b: GraphMeasurementEnvironment, c?: { local: boolean }): Promise<readonly LabelMetrics[]>;
        } }).laxGraphMeasure;
        const localMetrics = await measurement.measureLabels(input, env);
        const localVersioned = await measurement.measureLabels(input, env, { local: true });
        const namespace = "http://www.w3.org/2000/svg";
        const svg = document.createElementNS(namespace, "svg");
        svg.setAttribute("width", "800"); svg.setAttribute("height", "600");
        document.body.appendChild(svg);
        const boxes = reference.map((metric, index) => {
          const text = document.createElementNS(namespace, "text");
          text.setAttribute("id", `measured-${index}`);
          text.setAttribute("font-family", env.fontFamily);
          text.setAttribute("font-size", "12");
          text.setAttribute("font-weight", String(input[index]!.fontWeight ?? 400));
          text.setAttribute("letter-spacing", String(input[index]!.letterSpacing ?? 0));
          text.setAttribute("font-kerning", "normal");
          text.setAttribute("text-rendering", "geometricPrecision");
          text.style.fontKerning = "normal";
          text.style.lineHeight = "16px";
          text.style.fontSynthesis = "none";
          text.style.setProperty("-webkit-font-smoothing", "antialiased");
          text.style.whiteSpace = "pre";
          svg.appendChild(text);
          return metric.lines.map((line) => {
            const tspan = document.createElementNS(namespace, "tspan");
            tspan.setAttribute("x", String(line.x)); tspan.setAttribute("y", String(line.y));
            tspan.textContent = line.text; text.appendChild(tspan);
            const box = tspan.getBBox();
            return { x: box.x, y: box.y, width: box.width, height: box.height };
          });
        });
        return { boxes, localMetrics, localVersioned };
      }, { requests, metrics, env: measurer.environment });
      // Chromium's font provenance proves no system fallback drew the tested
      // labels. Glyph coverage metadata is tested separately before launching.
      const session = await context.newCDPSession(page);
      await session.send("DOM.enable"); await session.send("CSS.enable");
      const document = await session.send("DOM.getDocument");
      const { nodeId } = await session.send("DOM.querySelector", { nodeId: document.root.nodeId, selector: "#measured-1" });
      const { fonts } = await session.send("CSS.getPlatformFontsForNode", { nodeId });
      expect(fonts.length).toBeGreaterThan(1);
      expect(fonts.every((font) => font.isCustomFont)).toBe(true);
      expect(result.localMetrics).toEqual(metrics);
      result.boxes.forEach((boxes, index) => boxes.forEach((box, lineIndex) => {
        const ink = metrics[index]!.lines[lineIndex]!.ink;
        for (const key of ["x", "y", "width", "height"] as const) expect(box[key]).toBeCloseTo(ink[key], 5);
      }));
      result.localVersioned.forEach((metric, index) => {
        expect(metric.signature).not.toBe(metrics[index]!.signature);
        expect({ ...metric, signature: metrics[index]!.signature }).toEqual(metrics[index]);
      });
    } finally { await context.close(); }
  });

  it("rejects a mismatched browser pin rather than accepting unstable metrics", async () => {
    const wrongPin = createGraphMeasurer({ executablePath: executable, expectedBrowserVersion: "0.0.0.0" });
    await expect(wrongPin.measureLabels([{ text: "Alpha", maxWidth: 240 }])).rejects.toThrow(/GRAPH_BROWSER_VERSION_MISMATCH/u);
    await wrongPin.close();
  });
});

if (!executable) it("exact graph browser checks skipped: provision pinned Chromium and set GRAPH_CHROME", () => {
  expect(executable).toBeUndefined();
});
