import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { generateSite } from "../src/sitegen/generate.js";
import { page } from "../src/sitegen/html.js";
import { tmpDir } from "./helpers.js";

describe("workshop page", () => {
  it("generates the invitation and Google Forms preregistration at /workshop", async () => {
    const root = tmpDir("lax-site-workshop-");
    await generateSite([], root);
    const html = fs.readFileSync(path.join(root, "workshop", "index.html"), "utf8");

    expect(html).toContain("Lean and Lax online workshop");
    expect(html).not.toContain("laxarchive.org/workshop");
    expect(html).toContain('<h2 id="workshop-outcomes-heading">We offer a free online workshop that teaches:</h2>');
    expect(html).not.toContain("What you will learn");
    expect(html).toContain("How to get started with Lean.");
    expect(html).toContain("Claude Code or OpenAI Codex");
    expect(html).toContain("share these results with the community using Lax");
    expect(html).toContain('<ul class="workshop-highlights" aria-label="Workshop at a glance">');
    expect(html).toContain("All Lean levels");
    expect(html).toContain("xx.xx.xxxx");
    expect(html).toContain("10:00–12:00 CET");
    expect(html).toContain("xxxx.zoom");
    expect(html).toContain("name, email address, and prior Lean knowledge");
    expect(html).not.toContain("workshop-registration-heading");
    expect(html).toContain('<section class="workshop-registration" aria-label="Workshop registration">');
    expect(html).toContain('<iframe src="https://docs.google.com/forms/d/e/1FAIpQLScCkCORYWuaP9SvNeySxIsa_zEuqTz8q_d9b8-3SOxS1L_xIg/viewform?embedded=true" width="100%" height="1400" frameborder="0"');
    expect(html).toContain('title="Lean and Lax workshop preregistration form"');
    expect(html).not.toContain("Open preregistration form");
    expect(html).toContain("frame-src https://comments.laxarchive.org https://accounts.google.com https://docs.google.com");
    expect(html).toContain('href="../assets/style.css');
    expect(html).toContain('href="../index.html"');
  });

  it("keeps the Google Forms frame permission off other pages", () => {
    const html = page({ title: "Ordinary", rootRel: "", sidebar: "", content: "" });
    expect(html).not.toContain("docs.google.com");
  });

  it("rejects non-origin or non-HTTPS frame permissions", () => {
    expect(() => page({
      title: "Unsafe",
      rootRel: "",
      sidebar: "",
      content: "",
      frameOrigins: ["https://example.com/path"],
    })).toThrow("frame origin must be an exact HTTPS origin");
  });
});
