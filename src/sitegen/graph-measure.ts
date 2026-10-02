/** Host service for exact graph text measurement. The core layout package
 * knows only the resulting sizes; it has no dependency on this DOM host. */
import fs from "node:fs";
import path from "node:path";
import { createHash, randomUUID } from "node:crypto";
import { performance } from "node:perf_hooks";
import { siteAssetPath } from "./assets.js";
import type { Rect } from "../graph-layout/types.js";

export const GRAPH_MEASUREMENT_VERSION = "svg-labels-2";
export const GRAPH_LABEL_FONT_FAMILY = "'Latin Modern', 'Latin Modern Math', 'Lax Graph Fallback'";
/** Changes to this pin deliberately invalidate measurement caches. Archive CI
 * provisions the executable separately; installing the npm renderer never does. */
export const PINNED_GRAPH_BROWSER_VERSION = "150.0.7871.124";

export type LabelMeasureRequest = Readonly<{
  text: string; maxWidth: number;
  fontSize?: number; fontWeight?: 400 | 700; letterSpacing?: number; lineHeight?: number;
}>;
export type NormalizedLabelRequest = Readonly<Required<LabelMeasureRequest>>;
export type LabelMetrics = Readonly<{
  /** The complete permission-filtered input, including original whitespace. */
  text: string; width: number; height: number; signature: string;
  /** One SVG tspan per line. x/y are label-local origins and actual baselines;
   * ink is a conservative SVG glyph box in that same coordinate system. */
  lines: readonly Readonly<{ text: string; x: number; y: number; ink: Rect }>[];
}>;
export type GraphFontFace = Readonly<{
  family: string; file: string; weight: number; sha256: string;
  coverage: readonly (readonly [number, number])[];
  /** Optional self-contained data URL for a local file export. */
  url?: string;
}>;
export type GraphMeasurementEnvironment = Readonly<{
  schemaVersion: 1; measurementVersion: string;
  fontFamily: string; fontSignature: string; fontFaceSignature: string;
  providerId: string; signature: string;
  fontFaces: readonly GraphFontFace[];
  /** Local pages can omit this: the helper uses its own script's directory. */
  assetBaseUrl?: string;
}>;
/** A host may inject an exact SVG measurement implementation. It receives only
 * public display labels. Its providerId must change if shaping behavior changes. */
export type MeasureLabelsProvider = (
  requests: readonly NormalizedLabelRequest[], environment: GraphMeasurementEnvironment,
) => Promise<readonly LabelMetrics[]>;
export type GraphMeasurementStatistics = Readonly<{
  requestedLabels: number; uniqueLabels: number; cacheHits: number;
  cacheMisses: number; corruptEntries: number; batches: number; browserLaunches: number;
  elapsedMs: number;
}>;
export type GraphMeasurer = Readonly<{
  environment: GraphMeasurementEnvironment;
  measureLabels(requests: readonly LabelMeasureRequest[]): Promise<readonly LabelMetrics[]>;
  close(): Promise<void>;
  readonly statistics: GraphMeasurementStatistics;
}>;
export type GraphMeasurerOptions = Readonly<{
  cacheDir?: string; executablePath?: string; expectedBrowserVersion?: string;
  /** Local library callers may opt out of launching a host browser while
   * retaining exact cache hits and an explicitly injected provider. */
  hostBrowser?: boolean;
  provider?: MeasureLabelsProvider; providerId?: string;
  /** A batching work limit, not a graph-size or label-size cutoff. */
  batchSize?: number;
}>;

export class GraphMeasurementError extends Error {
  constructor(readonly code: string, message: string) {
    super(`${code}: ${message}`);
    this.name = "GraphMeasurementError";
  }
}
/** Only this failure category authorizes the caller's explicit local-preview
 * fallback. Bad glyphs, corrupt fonts and mismatched pins remain diagnostics. */
export class GraphMeasurementUnavailableError extends GraphMeasurementError {
  constructor(message: string) {
    super("GRAPH_MEASUREMENT_UNAVAILABLE", message);
    this.name = "GraphMeasurementUnavailableError";
  }
}

function sha(value: string | Buffer): string { return createHash("sha256").update(value).digest("hex"); }
function freeze<T>(value: T): T {
  if (value !== null && typeof value === "object") {
    Object.freeze(value);
    for (const nested of Object.values(value)) freeze(nested);
  }
  return value;
}

export function normalizeLabelRequest(request: LabelMeasureRequest): NormalizedLabelRequest {
  const result = {
    text: request.text, maxWidth: request.maxWidth,
    fontSize: request.fontSize ?? 12, fontWeight: request.fontWeight ?? 400,
    letterSpacing: request.letterSpacing ?? 0, lineHeight: request.lineHeight ?? 16,
  };
  if (typeof result.text !== "string" || !Number.isFinite(result.maxWidth) || result.maxWidth <= 0 ||
      !Number.isFinite(result.fontSize) || result.fontSize <= 0 ||
      ![400, 700].includes(result.fontWeight) || !Number.isFinite(result.letterSpacing) ||
      result.letterSpacing < 0 || !Number.isFinite(result.lineHeight) || result.lineHeight <= 0) {
    throw new GraphMeasurementError("GRAPH_LABEL_REQUEST", "invalid text, dimensions or font style");
  }
  return Object.freeze(result);
}

function fontManifest(): readonly GraphFontFace[] {
  const manifest = JSON.parse(fs.readFileSync(siteAssetPath("graph-fonts.json"), "utf8")) as
    { schemaVersion: number; fonts: GraphFontFace[] };
  if (manifest.schemaVersion !== 1 || !Array.isArray(manifest.fonts) || !manifest.fonts.length) {
    throw new GraphMeasurementError("GRAPH_FONT_MANIFEST", "unsupported font coverage manifest");
  }
  for (const face of manifest.fonts) {
    if (sha(fs.readFileSync(siteAssetPath(face.file))) !== face.sha256) {
      throw new GraphMeasurementError("GRAPH_FONT_INTEGRITY", `${face.file} does not match its coverage manifest`);
    }
    let previous = -1;
    for (const [start, end] of face.coverage) {
      if (!Number.isSafeInteger(start) || !Number.isSafeInteger(end) || start <= previous || start > end || end > 0x10ffff) {
        throw new GraphMeasurementError("GRAPH_FONT_MANIFEST", `invalid coverage intervals in ${face.file}`);
      }
      previous = end;
    }
  }
  return freeze(manifest.fonts);
}

export function graphFontSignature(): string { return sha(JSON.stringify(fontManifest())); }

/** CSS face declarations participate in font selection even when all glyphs
 * come from the same loaded font bytes. Preserve their cascade order, while
 * excluding unrelated colors/layout decoration from the measurement key. */
export function graphFontFaceSignature(stylesheet = fs.readFileSync(siteAssetPath("style.css"), "utf8")): string {
  const withoutComments = stylesheet.replace(/\/\*[\s\S]*?\*\//gu, "");
  return sha(JSON.stringify(withoutComments.match(/@font-face\s*\{[^}]*\}/gu) ?? []));
}

export function graphMeasurementEnvironment(providerId = `chromium:${PINNED_GRAPH_BROWSER_VERSION}`): GraphMeasurementEnvironment {
  const fontFaces = fontManifest();
  const fontSignature = sha(JSON.stringify(fontFaces));
  const fontFaceSignature = graphFontFaceSignature();
  const signature = sha(JSON.stringify([GRAPH_MEASUREMENT_VERSION, providerId, GRAPH_LABEL_FONT_FAMILY,
    fontSignature, fontFaceSignature, sha(fs.readFileSync(siteAssetPath("graph-measure-local.js")))]));
  return freeze({ schemaVersion: 1, measurementVersion: GRAPH_MEASUREMENT_VERSION,
    fontFamily: GRAPH_LABEL_FONT_FAMILY, fontSignature, fontFaceSignature, fontFaces, providerId, signature });
}

/** This field order is shared with graph-measure-local.js and tested against it. */
export function graphMeasurementKey(input: LabelMeasureRequest, environmentSignature: string): string {
  const request = normalizeLabelRequest(input);
  return sha(JSON.stringify([environmentSignature, request.text, request.maxWidth, request.fontSize,
    request.fontWeight, request.letterSpacing, request.lineHeight]));
}

function containsCodePoint(ranges: readonly (readonly [number, number])[], code: number): boolean {
  let lo = 0, hi = ranges.length;
  while (lo < hi) {
    const middle = (lo + hi) >>> 1, [start, end] = ranges[middle]!;
    if (code < start) hi = middle;
    else if (code > end) lo = middle + 1;
    else return true;
  }
  return false;
}

export function assertGraphGlyphCoverage(input: LabelMeasureRequest, environment: GraphMeasurementEnvironment): void {
  const request = normalizeLabelRequest(input);
  const fonts = environment.fontFaces.filter((face) => face.family !== "Latin Modern" || face.weight === request.fontWeight);
  const missing = new Set<number>();
  for (const char of request.text) {
    if (/^[\t\n\r ]$/u.test(char)) continue;
    const code = char.codePointAt(0)!;
    if (!fonts.some((font) => containsCodePoint(font.coverage, code))) missing.add(code);
  }
  if (missing.size) throw new GraphMeasurementError("GRAPH_LABEL_GLYPH_UNSUPPORTED", "bundled graph fonts lack " +
    [...missing].sort((a, b) => a - b).map((code) => `U+${code.toString(16).toUpperCase().padStart(4, "0")}`).join(", "));
}

/** The glyph drawn for a code point outside the bundled fonts: the tofu box
 * every browser would show anyway, but measured and drawn deterministically. */
export const GRAPH_MISSING_GLYPH = "\u25A1";

/** Replace every code point the bundled fonts cannot draw with the tofu box,
 * so an author's title in any script still yields an exactly measured label.
 * The original text stays in the page; only the figure's label changes. */
export function substituteUnsupportedGlyphs(input: LabelMeasureRequest, environment: GraphMeasurementEnvironment):
    { text: string; missing: readonly number[] } {
  const request = normalizeLabelRequest(input);
  const fonts = environment.fontFaces.filter((face) => face.family !== "Latin Modern" || face.weight === request.fontWeight);
  const covered = (code: number) => fonts.some((font) => containsCodePoint(font.coverage, code));
  const missing = new Set<number>();
  let text = "";
  for (const char of request.text) {
    const code = char.codePointAt(0)!;
    if (/^[\t\n\r ]$/u.test(char) || covered(code)) { text += char; continue; }
    missing.add(code);
    text += GRAPH_MISSING_GLYPH;
  }
  if (missing.size && !covered(GRAPH_MISSING_GLYPH.codePointAt(0)!)) {
    throw new GraphMeasurementError("GRAPH_FONT_MANIFEST", "bundled graph fonts lack the missing-glyph box U+25A1");
  }
  return { text, missing: [...missing].sort((a, b) => a - b) };
}

/** Independent host validation protects both injected providers and disk hits.
 * Geometry remains exact browser output; this does not estimate its dimensions. */
export function validateLabelMetrics(value: unknown, request: LabelMeasureRequest, signature: string): value is LabelMetrics {
  if (!value || typeof value !== "object") return false;
  const metric = value as LabelMetrics;
  if (metric.text !== request.text || metric.signature !== signature || !Number.isFinite(metric.width) || metric.width < 0 ||
      !Number.isFinite(metric.height) || metric.height <= 0 || !Array.isArray(metric.lines) || !metric.lines.length) return false;
  let previousY = -Infinity;
  for (const line of metric.lines) {
    if (typeof line.text !== "string" || !Number.isFinite(line.x) || !Number.isFinite(line.y) ||
        line.x < 0 || line.y < previousY || !line.ink) return false;
    const box = line.ink;
    if (![box.x, box.y, box.width, box.height].every(Number.isFinite) ||
        box.x < -1e-6 || box.y < -1e-6 || box.width < 0 || box.height < 0 ||
        box.x + box.width > metric.width + 1e-6 || box.y + box.height > metric.height + 1e-6) return false;
    previousY = line.y;
  }
  // A wrapped identifier can cross a line without spaces. Ignore display
  // whitespace here while requiring preservation of every non-whitespace glyph.
  return metric.lines.map((line) => line.text).join("").replace(/\s/gu, "") === request.text.replace(/\s/gu, "");
}

type BrowserProvider = Readonly<{ measure: MeasureLabelsProvider; close(): Promise<void> }>;

async function browserProvider(options: GraphMeasurerOptions, onLaunch: () => void): Promise<BrowserProvider> {
  if (options.hostBrowser === false) throw new GraphMeasurementUnavailableError(
    "host browser measurement is disabled for this local caller; use exact cached labels, an injected provider, or the packaged local browser path");
  let chromium: typeof import("playwright-core")["chromium"];
  try { ({ chromium } = await import("playwright-core")); }
  catch {
    throw new GraphMeasurementUnavailableError("the archive measurement host needs playwright-core; " +
      "install the development tooling or inject an exact measureLabels provider. Local previews can use the packaged first-party browser path.");
  }
  const executablePath = options.executablePath ?? process.env.GRAPH_CHROME ?? "/usr/bin/google-chrome";
  const expected = options.expectedBrowserVersion ?? process.env.GRAPH_CHROME_VERSION ?? PINNED_GRAPH_BROWSER_VERSION;
  let browser: Awaited<ReturnType<typeof chromium.launch>>;
  try {
    browser = await chromium.launch({ executablePath, headless: true,
      args: ["--no-sandbox", "--font-render-hinting=none"] });
  } catch (error) {
    throw new GraphMeasurementUnavailableError(`cannot start the pinned browser at ${executablePath}: ${String(error)}`);
  }
  onLaunch();
  try {
    if (browser.version() !== expected) throw new GraphMeasurementError("GRAPH_BROWSER_VERSION_MISMATCH",
      `expected ${expected}, found ${browser.version()}; provision the pinned browser or explicitly version the measurement host`);
    const context = await browser.newContext({ viewport: { width: 1280, height: 800 }, deviceScaleFactor: 1,
      locale: "en-US", timezoneId: "UTC", reducedMotion: "reduce" });
    const fontFiles = new Set(fontManifest().map((face) => `/${face.file}`));
    await context.route("**/*", async (route) => {
      const url = new URL(route.request().url());
      if (url.origin !== "https://lax-graph-measure.invalid") { await route.abort(); return; }
      if (url.pathname === "/") {
        await route.fulfill({ contentType: "text/html", body: '<!doctype html><meta charset="utf-8">' +
          '<link rel="stylesheet" href="style.css"><body><script src="graph-measure-local.js"></script></body>' });
      } else if (["/style.css", "/graph-measure-local.js"].includes(url.pathname) || fontFiles.has(url.pathname)) {
        await route.fulfill({ contentType: url.pathname.endsWith(".css") ? "text/css" :
          url.pathname.endsWith(".js") ? "text/javascript" : "font/woff2",
        body: fs.readFileSync(siteAssetPath(url.pathname.slice(1))) });
      } else await route.abort();
    });
    const page = await context.newPage();
    await page.goto("https://lax-graph-measure.invalid/");
    return {
      measure: async (requests, environment) => {
        try {
          return await page.evaluate(async ({ requests: labels, environment: env }) => {
            const host = globalThis as unknown as {
              laxGraphMeasure: { measureLabels(a: typeof labels, b: typeof env): Promise<readonly LabelMetrics[]> };
            };
            return host.laxGraphMeasure.measureLabels(labels, env);
          }, { requests, environment });
        } catch (error) {
          const message = String(error), code = /\b(GRAPH_[A-Z_]+):/u.exec(message)?.[1] ?? "GRAPH_MEASUREMENT_BROWSER";
          throw new GraphMeasurementError(code, message);
        }
      },
      close: () => browser.close(),
    };
  } catch (error) { await browser.close(); throw error; }
}

/** One build service, one lazily launched browser, all labels batched and
 * content-cached. Its diagnostics/statistics never enter canonical geometry. */
export function createGraphMeasurer(options: GraphMeasurerOptions = {}): GraphMeasurer {
  const expected = options.expectedBrowserVersion ?? process.env.GRAPH_CHROME_VERSION ?? PINNED_GRAPH_BROWSER_VERSION;
  if (options.provider && !options.providerId) throw new GraphMeasurementError("GRAPH_PROVIDER_ID", "an injected provider needs its stable versioned providerId");
  const environment = graphMeasurementEnvironment(options.providerId ?? `chromium:${expected}`);
  const batchSize = options.batchSize ?? 256;
  if (!Number.isSafeInteger(batchSize) || batchSize < 1) throw new GraphMeasurementError("GRAPH_LABEL_BATCH", "batchSize must be a positive integer");
  const memory = new Map<string, LabelMetrics>();
  const stats = { requestedLabels: 0, uniqueLabels: 0, cacheHits: 0, cacheMisses: 0,
    corruptEntries: 0, batches: 0, browserLaunches: 0, elapsedMs: 0 };
  let browser: Promise<BrowserProvider> | undefined;
  let queue: Promise<unknown> = Promise.resolve(), closed = false;

  function readCache(key: string, request: NormalizedLabelRequest): LabelMetrics | undefined {
    if (!options.cacheDir) return undefined;
    const file = path.join(options.cacheDir, `${key}.json`);
    try {
      const cached = JSON.parse(fs.readFileSync(file, "utf8")) as { schemaVersion: number; key: string; digest: string; metric: unknown };
      if (cached.schemaVersion !== 1 || cached.key !== key || cached.digest !== sha(JSON.stringify(cached.metric)) ||
          !validateLabelMetrics(cached.metric, request, key)) throw new Error("invalid cached label");
      return freeze(cached.metric);
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code !== "ENOENT") stats.corruptEntries++;
      return undefined;
    }
  }
  function writeCache(key: string, metric: LabelMetrics): void {
    if (!options.cacheDir) return;
    fs.mkdirSync(options.cacheDir, { recursive: true });
    const file = path.join(options.cacheDir, `${key}.json`), temporary = `${file}.${randomUUID()}.tmp`;
    const bytes = JSON.stringify({ schemaVersion: 1, key, digest: sha(JSON.stringify(metric)), metric }) + "\n";
    try { fs.writeFileSync(temporary, bytes); fs.renameSync(temporary, file); }
    finally { if (fs.existsSync(temporary)) fs.unlinkSync(temporary); }
  }
  async function measure(input: readonly LabelMeasureRequest[]): Promise<readonly LabelMetrics[]> {
    const started = performance.now();
    try {
      const requests = input.map(normalizeLabelRequest);
      requests.forEach((request) => assertGraphGlyphCoverage(request, environment));
      stats.requestedLabels += requests.length;
      const keys = requests.map((request) => graphMeasurementKey(request, environment.signature));
      const missing = new Map<string, NormalizedLabelRequest>();
      keys.forEach((key, index) => {
        if (missing.has(key)) return;
        const metric = memory.get(key) ?? readCache(key, requests[index]!);
        if (metric) { memory.set(key, metric); stats.cacheHits++; }
        else { missing.set(key, requests[index]!); stats.cacheMisses++; }
      });
      const pending = [...missing];
      for (let offset = 0; offset < pending.length; offset += batchSize) {
        const batch = pending.slice(offset, offset + batchSize);
        let provider = options.provider;
        if (!provider) {
          browser ??= browserProvider(options, () => { stats.browserLaunches++; });
          provider = (await browser).measure;
        }
        const result = await provider(batch.map(([, request]) => request), environment);
        stats.batches++;
        if (!Array.isArray(result) || result.length !== batch.length) {
          throw new GraphMeasurementError("GRAPH_LABEL_RESULT", "measurement provider returned an incomplete batch");
        }
        result.forEach((metric, index) => {
          const [key, request] = batch[index]!;
          if (!validateLabelMetrics(metric, request, key)) {
            throw new GraphMeasurementError("GRAPH_LABEL_RESULT", `invalid or incomplete measured geometry for label ${key}`);
          }
          const frozen = freeze(metric);
          memory.set(key, frozen); writeCache(key, frozen);
        });
      }
      stats.uniqueLabels = memory.size;
      return Object.freeze(keys.map((key) => memory.get(key)!));
    } finally { stats.elapsedMs += performance.now() - started; }
  }
  return Object.freeze({ environment,
    measureLabels(requests: readonly LabelMeasureRequest[]) {
      if (closed) return Promise.reject(new GraphMeasurementError("GRAPH_MEASUREMENT_CLOSED", "measurement service is closed"));
      // Concurrent page preparation still uses exactly one browser/session.
      const next = queue.then(() => measure(requests));
      queue = next.catch(() => {});
      return next;
    },
    async close() {
      closed = true;
      await queue;
      if (browser) { const instance = await browser.catch(() => undefined); await instance?.close(); }
    },
    get statistics() { return Object.freeze({ ...stats }); },
  });
}
