import fs from "node:fs";
import path from "node:path";
import { chromium, firefox, webkit } from "playwright-core";
import { describe, expect, it } from "vitest";
import { highlightSource } from "../src/sitegen/highlight.js";
import { siteAssetPath } from "../src/sitegen/assets.js";

const browserName = (process.env.GRAPH_BROWSER ?? "chromium") as "chromium" | "firefox" | "webkit";
describe.runIf(Boolean(process.env.GRAPH_CHROME))("Lean hover interaction", () => {
  it("keeps type panels legible, keyboard-accessible and within the viewport without external requests", async () => {
    const browser = await { chromium, firefox, webkit }[browserName].launch({ headless: true,
      ...(browserName === "chromium" ? { executablePath: process.env.GRAPH_CHROME, args: ["--no-sandbox"] } : {}),
    });
    try {
      const page = await browser.newPage({ viewport: { width: 390, height: 300 } });
      const source = "def x := 1", type = "x : Nat\n<script>literal text</script>";
      const rows = await highlightSource(source, [], new Set(), { hovers: [{ start: 4, end: 5, text: type }] });
      const requests: string[] = [];
      await page.route("**/*", async route => {
        const url = new URL(route.request().url()); requests.push(url.href);
        if (url.pathname === "/") await route.fulfill({ contentType: "text/html", body:
          `<!doctype html><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'self' 'unsafe-inline'; script-src 'self'; font-src 'self'"><link rel="stylesheet" href="style.css"><style>table{position:absolute;right:8px;bottom:8px}</style><table class="inline-contract-table">${rows}</table><script src="lean-code.js" defer></script>` });
        else if (["style.css", "lean-code.js"].includes(path.basename(url.pathname)))
          await route.fulfill({ contentType: url.pathname.endsWith(".css") ? "text/css" : "text/javascript", body: fs.readFileSync(siteAssetPath(path.basename(url.pathname))) });
        else await route.abort();
      });
      await page.goto("https://lean-hover.test/");
      const token = page.locator("[data-lean-type]"), panel = page.locator(".lean-type-tooltip");
      await token.hover();
      await expect.poll(() => panel.isVisible()).toBe(true);
      expect(await panel.textContent()).toBe(type);
      expect(await panel.locator("script").count()).toBe(0);
      expect(await token.getAttribute("title")).toBeNull();
      const bounds = await panel.boundingBox();
      expect(bounds!.x).toBeGreaterThanOrEqual(0); expect(bounds!.y).toBeGreaterThanOrEqual(0);
      expect(bounds!.x + bounds!.width).toBeLessThanOrEqual(390);
      expect(bounds!.y + bounds!.height).toBeLessThanOrEqual(300);
      expect(await panel.evaluate(el => getComputedStyle(el).backgroundColor)).toBe("rgb(255, 255, 255)");
      await page.keyboard.press("Escape"); expect(await panel.isHidden()).toBe(true);
      await token.focus(); await expect.poll(() => panel.isVisible()).toBe(true);
      expect(await token.getAttribute("aria-describedby")).toBe("lean-type-tooltip");
      await page.keyboard.press("Escape"); expect(await token.getAttribute("aria-describedby")).toBeNull();
      expect(requests.every(url => url.startsWith("https://lean-hover.test/"))).toBe(true);
    } finally { await browser.close(); }
  }, 30_000);
});
