import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { generateSite } from "../src/sitegen/generate.js";
import { page } from "../src/sitegen/html.js";
import { tmpDir } from "./helpers.js";

describe("footer and legal pages", () => {
  it("links the legal pages from root and nested pages, and the about page from the header", () => {
    const rootPage = page({ title: "Root", rootRel: "", sidebar: "", content: "" });
    const nestedPage = page({ title: "Nested", rootRel: "../", sidebar: "", content: "" });

    for (const [html, prefix] of [[rootPage, ""], [nestedPage, "../"]] as const) {
      expect(html).toContain('<footer class="site-footer">');
      expect(html).toContain(`href="${prefix}impressum.html">Imprint</a>`);
      expect(html).toContain(`href="${prefix}privacy.html">Privacy</a>`);
      expect(html).not.toContain("lax-white-paper.pdf");
      expect(html).toContain(`<a class="site-nav-link" href="${prefix}about.html">About</a>`);
    }
  });

  it("generates both legal pages with the project-specific disclosures", async () => {
    const root = tmpDir("lax-site-legal-");
    await generateSite([], root);

    const impressum = fs.readFileSync(path.join(root, "impressum.html"), "utf8");
    const privacy = fs.readFileSync(path.join(root, "privacy.html"), "utf8");

    expect(impressum).toContain('<h1 class="paper-title">Imprint</h1>');
    const about = fs.readFileSync(path.join(root, "about.html"), "utf8");
    expect(about).toContain('<h1 class="paper-title">About Lax</h1>');
    expect(about).toContain("<h2>Lax Submission</h2>");
    expect(about).toContain('<figure class="content-figure"><img src="assets/concept-proof.svg"');
    expect(about).toContain("<figcaption>Left: a concept file");
    expect(about).not.toContain("Placeholder");
    // no sidebar on a page that is not about a submission, and no toggle to summon one
    expect(about).toContain('<header class="site-header sidebar-hidden">');
    expect(about).not.toContain('id="sidebar-toggle"');
    // Without the introduction in the archive the header names only the about page.
    expect(about).not.toContain('>Introduction</a>');
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
