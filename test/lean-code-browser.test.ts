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
      const source = "def x := Nat", type = "x : Lax1.Base Nat\n<script>literal text</script>";
      const href = "https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Nat";
      const rows = await highlightSource(source, [], new Set(), {
        links: [{ start: 9, end: 12, href }],
        hovers: [{ start: 4, end: 5, text: type }, { start: 9, end: 12, text: "Nat : Type" }],
        typeLinks: text => text === type ? [
          { start: 4, end: 13, href: "../lax-1/Lax1.Base.html#L1" },
          { start: 14, end: 17, href },
        ] : [],
      });
      const requests: string[] = [];
      await page.route("**/*", async route => {
        const url = new URL(route.request().url()); requests.push(url.href);
        if (url.pathname === "/") await route.fulfill({ contentType: "text/html", body:
          `<!doctype html><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'self' 'unsafe-inline'; script-src 'self'; font-src 'self'; img-src 'self'"><link rel="stylesheet" href="style.css"><style>table{position:absolute;right:8px;bottom:8px}</style><table class="inline-contract-table">${rows}</table><script src="lean-code.js" defer></script>` });
        else if (["style.css", "lean-code.js", "lean-type-cursor.svg"].includes(path.basename(url.pathname)))
          await route.fulfill({ contentType: url.pathname.endsWith(".css") ? "text/css" : url.pathname.endsWith(".svg") ? "image/svg+xml" : "text/javascript", body: fs.readFileSync(siteAssetPath(path.basename(url.pathname))) });
        else if (url.pathname === "/lax-1/Lax1.Base.html")
          await route.fulfill({ contentType: "text/html", body: '<p id="L1">Archive declaration</p>' });
        else await route.abort();
      });
      await page.goto("https://lean-hover.test/");
      const token = page.locator(".lean-typed-identifier"), panel = page.locator(".lean-type-tooltip");
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
      expect(await token.evaluate(el => getComputedStyle(el).cursor)).toContain("lean-type-cursor.svg");
      await token.click();
      await page.locator("a[data-lean-type]").hover();
      await page.mouse.move(1, 1);
      await page.waitForTimeout(250);
      expect(await panel.isVisible()).toBe(true);
      expect(await panel.textContent()).toBe(type);
      expect(await panel.locator("a").first().getAttribute("href")).toBe("../lax-1/Lax1.Base.html#L1");
      expect(await panel.locator("a").last().getAttribute("href")).toBe(href);
      expect(await panel.locator("a").last().getAttribute("title")).toBe("lean ↗");
      await panel.click({ position: { x: 3, y: 3 } });
      expect(await panel.isVisible()).toBe(true);
      await page.setViewportSize({ width: 400, height: 310 });
      expect(await panel.isVisible()).toBe(true);
      await page.mouse.click(1, 1);
      expect(await panel.isHidden()).toBe(true);
      await token.click();
      await page.keyboard.press("Escape"); expect(await panel.isHidden()).toBe(true);
      await token.evaluate(el => (el as HTMLElement).blur());
      await token.focus(); await expect.poll(() => panel.isVisible()).toBe(true);
      expect(await token.getAttribute("aria-describedby")).toBe("lean-type-tooltip");
      await page.keyboard.press("Escape"); expect(await token.getAttribute("aria-describedby")).toBeNull();
      const constant = page.locator("a[data-lean-type]");
      await constant.hover();
      expect(await panel.textContent()).toBe("Nat : Type");
      expect(await constant.getAttribute("href")).toBe(href);
      expect(await constant.getAttribute("title")).toBe("lean ↗");
      expect(await constant.evaluate(el => getComputedStyle(el).cursor)).toBe("pointer");
      expect(await panel.locator("a").count()).toBe(0);
      await panel.click({ position: { x: 3, y: 3 } });
      await page.mouse.move(1, 1);
      await page.waitForTimeout(250);
      expect(await panel.isVisible()).toBe(true);
      expect(await panel.textContent()).toBe("Nat : Type");
      await token.click();
      await page.keyboard.press("Tab");
      expect(await panel.locator("a").first().evaluate(el => el === document.activeElement)).toBe(true);
      await page.keyboard.press("Escape");
      await token.click();
      await panel.locator("a").first().click();
      await expect.poll(() => page.url()).toBe("https://lean-hover.test/lax-1/Lax1.Base.html#L1");
      expect(requests.every(url => url.startsWith("https://lean-hover.test/"))).toBe(true);
      await page.goto("https://lean-hover.test/");
      await page.route(href.split("#")[0]!, route => route.fulfill({ contentType: "text/html", body: "Lean documentation" }));
      await page.locator("a[data-lean-type]").click();
      await expect.poll(() => page.url()).toBe(href);
    } finally { await browser.close(); }
  }, 30_000);
});
