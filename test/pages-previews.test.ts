import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { branchesFromRemoteHeads, buildIndex, previewSlug, prunePreviews, recordPreview } from "../.github/scripts/pages-previews.mjs";
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


describe("Pages preview retention", () => {
  const now = Date.parse("2026-09-16T12:00:00Z");
  const day = 24 * 60 * 60 * 1000;
  function preview(root: string, branch: string, age: number) {
    const directory = path.join(root, "previews", previewSlug(branch));
    fs.mkdirSync(directory, { recursive: true });
    fs.writeFileSync(path.join(directory, "index.html"), branch);
    fs.writeFileSync(path.join(directory, "preview.json"), JSON.stringify({
      branch, sha: "a".repeat(40), updatedAt: new Date(now - age * day).toISOString(),
    }));
    return directory;
  }

  it("reconciles missed deletions and expiry without touching production or renderers", () => {
    const root = tmpDir("lax-preview-retention-");
    fs.writeFileSync(path.join(root, "index.html"), "production");
    fs.mkdirSync(path.join(root, "_renderer"));
    fs.writeFileSync(path.join(root, "_renderer", "old.tgz"), "renderer");
    const active = preview(root, "active", 1);
    const deleted = preview(root, "deleted", 1);
    const expired = preview(root, "expired", 14);
    const incomplete = path.join(root, "previews", "incomplete");
    fs.mkdirSync(incomplete);
    expect(prunePreviews(root, new Set(["main", "active", "expired"]), now).sort()).toEqual(
      [previewSlug("deleted"), previewSlug("expired"), "incomplete"].sort(),
    );
    expect(fs.existsSync(active)).toBe(true);
    for (const directory of [deleted, expired, incomplete]) expect(fs.existsSync(directory)).toBe(false);
    expect(fs.readFileSync(path.join(root, "index.html"), "utf8")).toBe("production");
    expect(fs.readFileSync(path.join(root, "_renderer", "old.tgz"), "utf8")).toBe("renderer");
    buildIndex(root);
    const index = fs.readFileSync(path.join(root, "previews", "index.html"), "utf8");
    expect(index).toContain(previewSlug("active"));
    expect(index).not.toContain(previewSlug("deleted"));
    expect(prunePreviews(root, new Set(["main", "active"]), now)).toEqual([]);
  });

  it("retains only the five newest previews, with deterministic ties", () => {
    const root = tmpDir("lax-preview-count-");
    const branches = Array.from({ length: 7 }, (_, i) => `branch-${i}`);
    for (let i = 0; i < branches.length; i++) preview(root, branches[i]!, i);
    expect(prunePreviews(root, new Set(branches), now).sort()).toEqual(
      [previewSlug("branch-5"), previewSlug("branch-6")].sort(),
    );
    // A newly pushed formerly expired preview can return and displace the oldest.
    preview(root, "branch-6", 0);
    expect(prunePreviews(root, new Set(branches), now)).toEqual([previewSlug("branch-4")]);
  });

  it("refuses empty or malformed remote snapshots before cleanup", () => {
    const root = tmpDir("lax-preview-snapshot-");
    const active = preview(root, "active", 1);
    expect(() => prunePreviews(root, new Set(), now)).toThrow("nonempty branch snapshot");
    expect(fs.existsSync(active)).toBe(true);
    expect(branchesFromRemoteHeads(`${"a".repeat(40)}\trefs/heads/main\n${"b".repeat(40)}\trefs/heads/topic/test\n`))
      .toEqual(new Set(["main", "topic/test"]));
    for (const invalid of ["", "network error", `${"a".repeat(40)} refs/heads/main`]) {
      expect(() => branchesFromRemoteHeads(invalid)).toThrow("refusing preview cleanup");
    }
  });
});
