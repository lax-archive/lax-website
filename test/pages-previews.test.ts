import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { buildIndex, previewSlug, recordPreview } from "../.github/scripts/pages-previews.mjs";
import { tmpDir } from "./helpers.js";

describe("Pages branch previews", () => {
  it("builds stable, collision-resistant preview paths", () => {
    const nested = previewSlug("codex/idea");
    expect(nested).toMatch(/^codex--idea-[0-9a-f]{8}$/);
    expect(previewSlug("codex/idea")).toBe(nested);
    expect(previewSlug("codex-idea")).not.toBe(nested);
  });

  it("records previews and renders a shareable index", () => {
    const root = tmpDir("lax-pages-previews-");
    const branch = "codex/interactive-homepage";
    const slug = previewSlug(branch);
    fs.mkdirSync(path.join(root, "previews", slug), { recursive: true });
    fs.writeFileSync(path.join(root, "previews", slug, "index.html"), "preview");

    recordPreview(root, branch, "0123456789abcdef");
    buildIndex(root);

    const record = JSON.parse(fs.readFileSync(path.join(root, "previews", slug, "preview.json"), "utf8"));
    expect(record).toMatchObject({ branch, sha: "0123456789abcdef" });
    const index = fs.readFileSync(path.join(root, "previews", "index.html"), "utf8");
    expect(index).toContain(`href="./${slug}/"`);
    expect(index).toContain("codex/interactive-homepage");
    expect(index).toContain("0123456");
  });
});
