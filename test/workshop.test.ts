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

    expect(html).toContain("Lax Online Meeting");
    expect(html).toContain('<link rel="canonical" href="https://laxarchive.org/workshop/">');
    expect(html).toContain('<h2 id="workshop-outcomes-heading">We invite you to an online meeting</h2>');
    expect(html).not.toContain("What you will learn");
    expect(html).toContain("We will discuss the very basics of Lean;");
    expect(html).toContain("Claude Code or OpenAI Codex");
    expect(html).toContain("share these results with the community through Lax");
    expect(html).toContain('<ul class="workshop-highlights" aria-label="Meeting at a glance">');
    expect(html).toContain("No Lean knowledge needed");
    expect(html).toContain("30 September 2026");
    expect(html).toContain("10:00–11:30 CEST");
    expect(html).toContain("90 minutes");
    expect(html).not.toContain("Two hours");
    expect(html).toContain('<a href="https://tuwien.zoom.us/j/67821353815?pwd=raNkw7i2jbOsg7X3KGMaN20uaIx1QX.1">Join the meeting</a>');
    expect(html).toContain("<strong>Meeting ID:</strong> <code>678 2135 3815</code>");
    expect(html).toContain("<strong>Password:</strong> <code>9qMtgVc3</code>");
    expect(html).not.toContain("To be announced");
    expect(html).not.toContain("name, email address, and prior Lean knowledge");
    expect(html).not.toContain("fill in the preregistration form below");
    expect(html).not.toContain("workshop-registration-head");
    expect(html).not.toContain("workshop-registration-heading");
    expect(html).toContain('<section class="workshop-registration" aria-label="Meeting registration">');
    expect(html).toContain('<iframe src="https://docs.google.com/forms/d/e/1FAIpQLScCkCORYWuaP9SvNeySxIsa_zEuqTz8q_d9b8-3SOxS1L_xIg/viewform?embedded=true" width="640" height="840" frameborder="0" marginheight="0" marginwidth="0"');
    expect(html).toContain('title="Lax Online Meeting preregistration form"');
    expect(html).not.toContain("Open preregistration form");
    expect(html).toContain("frame-src https://comments.laxarchive.org https://accounts.google.com https://docs.google.com");
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
