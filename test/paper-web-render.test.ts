import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import type { AddressInfo } from "node:net";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { chromium, type Browser, type Page } from "playwright-core";
import { SITE_MIME } from "../src/sitegen/assets.js";
import { generateSite } from "../src/sitegen/generate.js";
import { tmpDir } from "./helpers.js";

// The real end-check: the fixture bundle rendered by the vendored viewer in
// headless Chromium, over HTTP so the page's own CSP governs every fetch.
// It needs a Playwright-provisioned Chromium and skips (loudly) without one
// — plain `npm test` on a machine without browsers stays green.
import { attachFixturePaper } from "./paper-web-archive.js";

function chromiumExecutable(): string | undefined {
  const roots = [process.env.PLAYWRIGHT_BROWSERS_PATH, "/opt/pw-browsers"].filter((root): root is string => Boolean(root));
  for (const root of roots) {
    if (!fs.existsSync(root)) continue;
    for (const dir of fs.readdirSync(root).filter((name) => /^chromium-\d+$/u.test(name)).sort().reverse()) {
      const candidate = path.join(root, dir, "chrome-linux", "chrome");
      if (fs.existsSync(candidate)) return candidate;
    }
  }
  return undefined;
}

const executable = chromiumExecutable();

describe.skipIf(!executable)("the reflow surface, rendered", () => {
  let browser: Browser;
  let server: http.Server;
  let base: string;
  const consoleErrors: string[] = [];
  const pageErrors: string[] = [];
  const failedRequests: string[] = [];

  beforeAll(async () => {
    const root = tmpDir("lax-site-rendered-");
    await generateSite(attachFixturePaper(), root, { log: () => {} });
    server = http.createServer((request, response) => {
      const relative = decodeURIComponent(new URL(request.url ?? "/", "http://localhost").pathname).replace(/^\/+/u, "");
      const file = path.resolve(root, relative);
      if (!file.startsWith(root + path.sep) || !fs.existsSync(file) || fs.statSync(file).isDirectory()) {
        response.writeHead(404).end("not found");
        return;
      }
      response.writeHead(200, { "content-type": SITE_MIME[path.extname(file)] ?? "application/octet-stream" });
      response.end(fs.readFileSync(file));
    });
    await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
    base = `http://127.0.0.1:${(server.address() as AddressInfo).port}`;
    browser = await chromium.launch({ executablePath: executable });
  }, 60_000);

  afterAll(async () => {
    await browser?.close();
    server?.close();
  });

  async function watch(page: Page): Promise<void> {
    // The account header pings its identity bridge from every page; that
    // cross-origin traffic is irrelevant here (and unreachable from CI), so
    // it is cut off. Same-origin failures — a 404ed font, a missing block
    // file — are the ones this page must never produce.
    await page.route((url) => !url.href.startsWith(base), (route) => route.abort());
    page.on("console", (message) => {
      // Resource-load failures carry no URL here; the response/requestfailed
      // channels below record the same-origin ones with their URLs.
      if (message.type() === "error" && !/^Failed to load resource/u.test(message.text())) consoleErrors.push(message.text());
    });
    page.on("pageerror", (error) => pageErrors.push(String(error)));
    page.on("requestfailed", (request) => {
      if (request.url().startsWith(base)) failedRequests.push(`${request.url()} ${request.failure()?.errorText ?? ""}`);
    });
    page.on("response", (response) => {
      if (response.url().startsWith(base) && response.status() >= 400) failedRequests.push(`${response.url()} HTTP ${response.status()}`);
    });
  }

  const lineCount = (page: Page) =>
    page.evaluate(() => document.querySelectorAll(".latex-block svg > text").length);

  it("paints SVG text, anchors the marks, places a card beside its passage, and reflows", async () => {
    const page = await browser.newPage({ viewport: { width: 1500, height: 1000 } });
    await watch(page);
    await page.goto(`${base}/lax-21/paper.html`, { waitUntil: "load" });
    await page.waitForSelector(".latex-block svg text tspan", { timeout: 20_000 });
    await page.waitForFunction(() => document.getElementById("manuscript-rail-reflow")?.classList.contains("manuscript-rail-live"));

    // Painted glyphs, and every mark surfaced as begin/end anchors with the
    // begin side owning the deep-link id.
    const wideLines = await lineCount(page);
    expect(wideLines).toBeGreaterThan(10);
    const anchors = await page.evaluate(() => [...document.querySelectorAll(".latex-anchor[data-mark]")].map((a) => ({
      id: a.id, mark: (a as HTMLElement).dataset.mark, side: (a as HTMLElement).dataset.side,
    })));
    for (const n of [1, 2, 3, 4]) {
      expect(anchors).toContainEqual({ id: `m${n}`, mark: String(n), side: "b" });
      expect(anchors).toContainEqual({ id: "", mark: String(n), side: "e" });
    }

    // The first card sits beside its passage: card top within a line or two
    // of the begin anchor (BAND_ABOVE plus stacking slack).
    const join = await page.evaluate(() => {
      const anchor = document.getElementById("m1")!.getBoundingClientRect();
      const card = document.getElementById("m1-card")!.getBoundingClientRect();
      return { anchorTop: anchor.top, cardTop: card.top, cardLeft: card.left, anchorLeft: anchor.left };
    });
    expect(Math.abs(join.cardTop - join.anchorTop)).toBeLessThan(80);
    expect(join.cardLeft).toBeGreaterThan(join.anchorLeft); // the rail, in the gutter
    // And its gutter band is drawn.
    expect(await page.evaluate(() => document.querySelectorAll("#manuscript-reflow-links path.manuscript-link").length)).toBe(4);

    // The reflow proof: a narrower viewport re-breaks into more lines.
    await page.setViewportSize({ width: 980, height: 1000 });
    await page.waitForFunction((previous) =>
      document.querySelectorAll(".latex-block svg > text").length !== previous, wideLines, { timeout: 20_000 });
    const narrowLines = await lineCount(page);
    expect(narrowLines).toBeGreaterThan(wideLines);

    // The card follows its passage through the reflow.
    await page.waitForFunction(() => {
      const anchor = document.getElementById("m1")?.getBoundingClientRect();
      const card = document.getElementById("m1-card")?.getBoundingClientRect();
      return anchor && card && Math.abs(card.top - anchor.top) < 80;
    });

    // The AGPL notice is on the rendered surface.
    expect(await page.evaluate(() => document.querySelector(".manuscript-reflow-notice a")?.getAttribute("href")))
      .toBe("https://github.com/radek-p/reflowtex");
    await page.close();
  }, 60_000);

  it("lands #m<n> deep links on the passage in the reflowed text", async () => {
    const page = await browser.newPage({ viewport: { width: 1500, height: 700 } });
    await watch(page);
    await page.goto(`${base}/lax-21/paper.html#m4`, { waitUntil: "load" });
    await page.waitForSelector(".latex-block svg text tspan", { timeout: 20_000 });
    await page.waitForFunction(() => {
      const anchor = document.getElementById("m4");
      if (!anchor) return false;
      const box = anchor.getBoundingClientRect();
      return box.top >= -5 && box.top <= window.innerHeight;
    }, undefined, { timeout: 20_000 });
    // The card opened with the deep link.
    expect(await page.evaluate(() => document.getElementById("m4-card")?.classList.contains("manuscript-card-expanded"))).toBe(true);
    await page.close();
  }, 60_000);

  it("saw no viewer errors, page errors, or failed requests anywhere above", () => {
    expect(pageErrors).toEqual([]);
    expect(consoleErrors).toEqual([]);
    expect(failedRequests).toEqual([]);
  });
});

if (!executable) {
  it("headless render end-check skipped: no Playwright Chromium found (set PLAYWRIGHT_BROWSERS_PATH)", () => {
    expect(executable).toBeUndefined();
  });
}
