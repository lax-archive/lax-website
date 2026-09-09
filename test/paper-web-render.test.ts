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
      for (const platform of ["chrome-linux", "chrome-linux64"]) {
        const candidate = path.join(root, dir, platform, "chrome");
        if (fs.existsSync(candidate)) return candidate;
      }
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

    // The standalone tikz figure IS rendered (its paragraph is body content
    // in the stream): sweep the page so every lazily painted segment has
    // intersected, then find the sanitized drawing with real ink in it.
    await page.evaluate(async () => {
      for (let y = 0; y <= document.body.scrollHeight; y += window.innerHeight / 2) {
        window.scrollTo(0, y);
        await new Promise((resolve) => setTimeout(resolve, 50));
      }
      window.scrollTo(0, 0);
    });
    await page.waitForSelector(".latex-block svg g.latex-picture", { timeout: 20_000 });
    const pictureMarkup = await page.evaluate(() => document.querySelector(".latex-block svg g.latex-picture")!.innerHTML);
    expect(pictureMarkup).toMatch(/<(?:path|g|use)\b/u);

    // The AGPL notice is on the rendered surface.
    expect(await page.evaluate(() => document.querySelector(".manuscript-reflow-notice a")?.getAttribute("href")))
      .toBe("https://github.com/radek-p/reflowtex");
    await page.close();
  }, 60_000);

  it("carries the fragment to the printed page's link, and back", async () => {
    const page = await browser.newPage({ viewport: { width: 1500, height: 700 } });
    await watch(page);
    await page.goto(`${base}/lax-21/paper.html#m2`, { waitUntil: "load" });
    expect(await page.evaluate(() => document.querySelector<HTMLAnchorElement>('.manuscript-view-link[href^="paper-pdf.html"]')!.getAttribute("href"))).toBe("paper-pdf.html#m2");
    await page.evaluate(() => { location.hash = "#m3"; });
    expect(await page.evaluate(() => document.querySelector<HTMLAnchorElement>('.manuscript-view-link[href^="paper-pdf.html"]')!.getAttribute("href"))).toBe("paper-pdf.html#m3");
    // The printed page's card owns the id, and its link back keeps it.
    await page.goto(`${base}/lax-21/paper-pdf.html#m3`, { waitUntil: "load" });
    expect(await page.evaluate(() => document.getElementById("m3")?.classList.contains("manuscript-card"))).toBe(true);
    expect(await page.evaluate(() => document.querySelector<HTMLAnchorElement>('.manuscript-view-link[href^="paper.html"]')!.getAttribute("href"))).toBe("paper.html#m3");
    await page.close();
  }, 60_000);

  it("on a narrow screen opens a card in the text under its passage, and closes it", async () => {
    const page = await browser.newPage({ viewport: { width: 400, height: 800 }, isMobile: true, hasTouch: true });
    await watch(page);
    await page.goto(`${base}/lax-21/paper.html`, { waitUntil: "load" });
    await page.waitForSelector(".latex-block svg text tspan", { timeout: 20_000 });
    await page.waitForFunction(() => document.querySelector("#manuscript-reflow-doc path.manuscript-hl") !== null, undefined, { timeout: 20_000 });
    // One column: the text spans the screen, the rail is gone, no card in
    // the text yet.
    const columns = await page.evaluate(() => ({
      doc: document.getElementById("manuscript-reflow-doc")!.getBoundingClientRect().width,
      rail: getComputedStyle(document.getElementById("manuscript-rail-reflow")!).display,
      inline: document.querySelectorAll(".manuscript-card-inline").length,
    }));
    expect(columns.doc).toBeGreaterThan(300);
    expect(columns.rail).toBe("none");
    expect(columns.inline).toBe(0);

    // Tap m1's passage: its card opens in the text, expanded, right after
    // the segment holding the tapped line — within the block, a line or so
    // below the passage's end (m1 is one paragraph).
    // m2 begins in the stream, so its region starts a few px above the
    // segment after its anchor (STREAM_PAD in manuscript-reflow.js).
    const m2Region = () => page.evaluate(() => {
      let segment = document.getElementById("m2")!.nextElementSibling!;
      while (segment.classList.contains("latex-anchor")) segment = segment.nextElementSibling!;
      const region = document.querySelector<SVGPathElement>('#manuscript-reflow-doc path.manuscript-hl[data-mark="2"]')!.getBoundingClientRect().top;
      return { segment: segment.getBoundingClientRect().top, region };
    });
    const m2Before = await m2Region();
    expect(Math.abs(m2Before.segment - 4 - m2Before.region)).toBeLessThan(2);
    const passage = await page.evaluate(() => {
      const anchor = document.getElementById("m1")!.getBoundingClientRect();
      return { x: anchor.left + 4, y: anchor.top - 6 };
    });
    await page.mouse.click(passage.x, passage.y);
    await page.waitForFunction(() => document.getElementById("m1-card")?.classList.contains("manuscript-card-inline"), undefined, { timeout: 10_000 });
    const opened = await page.evaluate(() => {
      const card = document.getElementById("m1-card")!;
      const end = document.querySelector<HTMLElement>('.latex-anchor[data-mark="1"][data-side="e"]')!;
      let segment = card.previousElementSibling!;
      while (segment.classList.contains("latex-anchor")) segment = segment.previousElementSibling!;
      const segmentBox = segment.getBoundingClientRect();
      const endTop = end.getBoundingClientRect().top;
      return {
        expanded: card.classList.contains("manuscript-card-expanded"),
        bodyHidden: card.querySelector<HTMLElement>(".manuscript-card-body")!.hidden,
        inBlock: card.closest(".latex-block") !== null,
        afterSegment: segment.tagName === "svg" && segmentBox.top <= endTop && endTop <= segmentBox.bottom,
        afterEnd: end.compareDocumentPosition(card) === Node.DOCUMENT_POSITION_FOLLOWING,
        drop: card.getBoundingClientRect().top - endTop,
        width: card.getBoundingClientRect().width,
      };
    });
    expect(opened.expanded).toBe(true);
    expect(opened.bodyHidden).toBe(false);
    expect(opened.inBlock).toBe(true);
    expect(opened.afterSegment).toBe(true);
    expect(opened.afterEnd).toBe(true);
    expect(opened.drop).toBeGreaterThan(0);
    expect(opened.drop).toBeLessThan(80);
    expect(opened.width).toBeGreaterThan(300);
    // The passages below moved down with the text (the viewer re-pinned
    // their anchors for the height change), and their highlights followed:
    // m2's region keeps its place on m2's anchor.
    await page.waitForFunction((before) => {
      let segment = document.getElementById("m2")!.nextElementSibling!;
      while (segment.classList.contains("latex-anchor")) segment = segment.nextElementSibling!;
      const top = segment.getBoundingClientRect().top;
      const region = document.querySelector<SVGPathElement>('#manuscript-reflow-doc path.manuscript-hl[data-mark="2"]')!.getBoundingClientRect().top;
      return top - before.segment > 60 && Math.abs(top - 4 - region) < 2;
    }, m2Before, { timeout: 10_000 });

    // The × closes it: back out of the text, into the (hidden) rail.
    await page.click("#m1-card .manuscript-card-toggle");
    await page.waitForFunction(() => document.getElementById("m1-card")!.parentElement!.id === "manuscript-rail-reflow", undefined, { timeout: 10_000 });
    expect(await page.evaluate(() => document.querySelectorAll(".manuscript-card-inline").length)).toBe(0);

    // A deep link opens in the text too.
    await page.goto(`${base}/lax-21/paper.html#m4`, { waitUntil: "load" });
    await page.waitForFunction(() => document.getElementById("m4-card")?.classList.contains("manuscript-card-inline"), undefined, { timeout: 20_000 });

    // Widening the screen moves the open card back beside the text.
    await page.setViewportSize({ width: 1400, height: 800 });
    await page.waitForFunction(() => {
      // Reflow can briefly detach the card; keep polling until it is placed.
      const card = document.getElementById("m4-card");
      return card?.parentElement?.id === "manuscript-rail-reflow" && card.classList.contains("manuscript-card-expanded") && card.style.top !== "";
    }, undefined, { timeout: 10_000 });
    await page.close();
  }, 90_000);

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
