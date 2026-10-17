import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { generateSite } from "../src/sitegen/generate.js";
import { page } from "../src/sitegen/html.js";
import { tmpDir } from "./helpers.js";

describe("workshop page", () => {
  it("shows only meeting materials at /workshop, retaining the invitation and form in a comment", async () => {
    const root = tmpDir("lax-site-workshop-");
    await generateSite([], root);
    const source = fs.readFileSync(path.join(root, "workshop", "index.html"), "utf8");
    const html = source.replace(/<!--[\s\S]*?-->/g, "");

    expect(html).toContain("<title>Material from the 1st Lax Online Meeting — Lax Lean Archive</title>");
    expect(html).toContain('<link rel="canonical" href="https://laxarchive.org/workshop/">');
    expect(html).not.toContain("2nd Lax Online Meeting");
    expect(html).not.toContain("workshop-hero");
    expect(html).not.toContain("workshop-summary");
    expect(html).not.toContain("workshop-registration");
    expect(html).not.toContain('src="https://docs.google.com/forms/');
    expect(source).toContain("<!-- Past meeting invitation and preregistration");
    expect(source).toContain('<h2 id="workshop-outcomes-heading">We invite you to an online meeting</h2>');
    expect(source).toContain('title="Lax Online Meeting preregistration form"');
    expect(html).toContain('<h1 id="workshop-material-heading">Material from the 1st Lax Online Meeting</h1>');
    expect(html).toContain("The first meeting took place on 30 September 2026.");
    expect(html).toContain('<iframe src="https://www.youtube-nocookie.com/embed/vx1IRXcA2bg"');
    expect(html).toContain('href="../assets/lax-online-meeting-2026-09-30.pdf"');
    expect(html).toContain('href="https://www.youtube.com/watch?v=vx1IRXcA2bg"');
    expect(html).toContain("frame-src https://comments.laxarchive.org https://accounts.google.com https://docs.google.com https://www.youtube-nocookie.com");
    expect(html).toContain('href="../assets/style.css');
    expect(html).toContain('href="../index.html"');
  });

  it("keeps the Google Forms frame permission off other pages", () => {
    const html = page({ title: "Ordinary", rootRel: "", canonicalPath: "ordinary.html", sidebar: "", content: "" });
    expect(html).not.toContain("docs.google.com");
  });

  it("rejects non-origin or non-HTTPS frame permissions", () => {
    expect(() => page({
      title: "Unsafe",
      rootRel: "",
      canonicalPath: "unsafe.html",
      sidebar: "",
      content: "",
      frameOrigins: ["https://example.com/path"],
    })).toThrow("frame origin must be an exact HTTPS origin");
  });
});
