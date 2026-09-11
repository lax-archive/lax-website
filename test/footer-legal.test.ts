import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { generateSite } from "../src/sitegen/generate.js";
import { page } from "../src/sitegen/html.js";
import { tmpDir } from "./helpers.js";

describe("footer and legal pages", () => {
  it("links the legal pages and whitepaper from root and nested pages", () => {
    const rootPage = page({ title: "Root", rootRel: "", sidebar: "", content: "" });
    const nestedPage = page({ title: "Nested", rootRel: "../", sidebar: "", content: "" });

    for (const [html, prefix] of [[rootPage, ""], [nestedPage, "../"]] as const) {
      expect(html).toContain('<footer class="site-footer">');
      expect(html).toContain(`href="${prefix}impressum.html">Imprint</a>`);
      expect(html).toContain(`href="${prefix}privacy.html">Privacy</a>`);
      expect(html).toContain(`href="${prefix}assets/lax-white-paper.pdf">About</a>`);
    }
  });

  it("generates both legal pages with the project-specific disclosures", async () => {
    const root = tmpDir("lax-site-legal-");
    await generateSite([], root);

    const impressum = fs.readFileSync(path.join(root, "impressum.html"), "utf8");
    const privacy = fs.readFileSync(path.join(root, "privacy.html"), "utf8");

    expect(impressum).toContain('<h1 class="paper-title">Imprint</h1>');
    expect(impressum).toContain("Service providers");
    expect(impressum).not.toContain("Anbieter und Verantwortlicher");
    expect(impressum).toContain("Clemens Kuske");
    expect(impressum).toContain("Jan Dreier");
    expect(impressum).toContain("Édouard Bonnet");
    expect(impressum).toContain("Prof.-Dr.-Helmert-Str. 2–3");
    expect(impressum).toContain("46 allée d'Italie");
    expect(impressum).toContain("mail@clemens-kuske.de");
    expect(privacy).toContain("Controllers");
    expect(privacy).toContain("Jan Dreier");
    expect(privacy).toContain("Édouard Bonnet");
    expect(privacy).toContain("GitHub Pages");
    expect(privacy).toContain("Amazon Web Services (AWS)");
    expect(privacy).toContain("ORCID iD");
    expect(privacy).toContain('<h1 class="paper-title">Privacy Notice</h1>');
    expect(privacy).toContain("for up to 14 days");
    expect(privacy).toContain("Section 25(2)(2) TDDDG");
    expect(privacy).not.toContain("Datenschutzerklärung");
  });
});
