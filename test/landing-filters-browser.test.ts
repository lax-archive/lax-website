import fs from "node:fs";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { chromium, type Browser } from "playwright-core";
import { siteAssetPath } from "../src/sitegen/assets.js";

// Real browser wrapping and focus behavior; no archive graph search is needed
// for this small filter fixture. The page producer is covered by sitegen tests.
const executable = process.env.GRAPH_CHROME;
describe.skipIf(!executable)("landing topic disclosure", () => {
  let browser: Browser;
  beforeAll(async () => { browser = await chromium.launch({ executablePath: executable, args: ["--no-sandbox"] }); });
  afterAll(async () => { await browser?.close(); });
  const chip = (key: string, label: string) => `<button class="tag-chip" data-tag-filter="${key}" aria-pressed="${!key}"><span>${label}</span><b>1</b></button>`;
  const html = `<!doctype html><link rel="stylesheet" href="/style.css"><script defer src="/sidebar.js"></script>
    <input id="filter-search"><input id="submissions-search"><ul id="entry-list"><li id="entry-list-empty" hidden></li></ul>
    <div class="tag-browser-heading">${chip("", "All submissions")}</div>
    <div class="environment-chip-list">${chip("v4.33.0", "v4.33.0 · epoch")}${chip("v4.30.0", "v4.30.0")}</div>
    <div class="tag-chip-list" id="topic-chip-list">${Array.from({ length: 24 }, (_, i) => chip(`topic-${i}`, `Parameterized graph problem ${i}`)).join("")}</div>
    <button id="tag-topics-toggle" aria-expanded="false" aria-controls="topic-chip-list" hidden>More topics</button>
    <p id="tag-results-status" aria-live="polite"></p>
    <ul id="submissions-list">${Array.from({ length: 24 }, (_, i) => `<li data-search-title="Submission ${i}" data-search-concepts="" data-search-order="${i}" data-state="registered" data-tags="|topic-${i}|${i % 2 ? "v4.30.0" : "v4.33.0"}|">Submission ${i}</li>`).join("")}<li id="submissions-list-empty" hidden>No matches</li></ul>
    <button id="submissions-load-more" hidden>Show all</button>`;
  async function open(query = "", javaScriptEnabled = true) {
    const context = await browser.newContext({ viewport: { width: 600, height: 900 }, javaScriptEnabled });
    const page = await context.newPage();
    await page.route("**/*", async (route) => {
      const name = new URL(route.request().url()).pathname.slice(1);
      if (!name) return route.fulfill({ contentType: "text/html", body: html });
      return route.fulfill({ contentType: name.endsWith(".css") ? "text/css" : name.endsWith(".js") ? "application/javascript" : "font/woff2", body: fs.readFileSync(siteAssetPath(name)) });
    });
    await page.goto(`https://landing-filters.test/${query}`);
    await page.evaluate(() => document.fonts.ready);
    return { page, context };
  }
  it("shows two topic rows, reveals every topic, and preserves filtering and history", async () => {
    const { page, context } = await open();
    try {
      const visible = () => page.locator('.tag-chip-list .tag-chip:not([hidden])');
      expect(await visible().evaluateAll((nodes) => new Set(nodes.map((n) => (n as HTMLElement).offsetTop)).size)).toBe(2);
      expect(await page.locator('.environment-chip-list [hidden]').count()).toBe(0);
      const more = page.locator('#tag-topics-toggle');
      await more.focus(); await page.keyboard.press("Enter");
      expect(await visible().count()).toBe(24);
      await page.locator('[data-tag-filter="topic-23"]').click();
      expect(new URL(page.url()).searchParams.get("tag")).toBe("topic-23");
      expect(await page.locator('#submissions-list [data-search-title]:not([hidden])').allTextContents()).toEqual(["Submission 23"]);
      await page.locator('[data-tag-filter="v4.33.0"]').click();
      expect(await page.locator('#submissions-list [data-search-title]:not([hidden])').allTextContents()).toEqual(["Submission 0", "Submission 2", "Submission 4"]);
      await page.goBack();
      expect(await page.locator('[data-tag-filter="topic-23"]').getAttribute("aria-pressed")).toBe("true");
      await page.setViewportSize({ width: 390, height: 900 });
      await more.click();
      expect(await visible().evaluateAll((nodes) => new Set(nodes.map((n) => (n as HTMLElement).offsetTop)).size)).toBe(2);
    } finally { await context.close(); }
  });
  it("reveals a topic selected by a saved URL, and leaves all topics available without JavaScript", async () => {
    const linked = await open("?tag=topic-23");
    try {
      expect(await linked.page.locator('#tag-topics-toggle').getAttribute("aria-expanded")).toBe("true");
      expect(await linked.page.locator('[data-tag-filter="topic-23"]').isVisible()).toBe(true);
    } finally { await linked.context.close(); }
    const plain = await open("", false);
    try {
      expect(await plain.page.locator('.tag-chip-list .tag-chip:visible').count()).toBe(24);
      expect(await plain.page.locator('#tag-topics-toggle').isVisible()).toBe(false);
    } finally { await plain.context.close(); }
  });
});
