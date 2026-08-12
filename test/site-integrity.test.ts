import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { INTEGRITY_FILE, writeIntegrityManifest } from "../.github/scripts/site-integrity.mjs";
import { tmpDir } from "./helpers.js";

describe("site publication integrity", () => {
  it("seals a deterministic, sorted inventory of the generated tree", () => {
    const root = tmpDir("lax-site-integrity-manifest-");
    fs.mkdirSync(path.join(root, "lax-2"));
    fs.writeFileSync(path.join(root, "lax-2", "index.html"), "submission");
    fs.writeFileSync(path.join(root, "index.html"), "archive");
    fs.writeFileSync(path.join(root, INTEGRITY_FILE), "stale manifest");

    const first = writeIntegrityManifest(root, "a".repeat(40), "b".repeat(40));
    const bytes = fs.readFileSync(path.join(root, INTEGRITY_FILE), "utf8");
    const second = writeIntegrityManifest(root, "a".repeat(40), "b".repeat(40));

    expect(second).toEqual(first);
    expect(fs.readFileSync(path.join(root, INTEGRITY_FILE), "utf8")).toBe(bytes);
    expect(first.files.map((file: { path: string }) => file.path)).toEqual(["index.html", "lax-2/index.html"]);
    expect(first.files[0]).toEqual({
      path: "index.html",
      bytes: 7,
      sha256: crypto.createHash("sha256").update("archive").digest("hex"),
    });
  });

  it("rejects provenance that is not an exact Git revision", () => {
    const root = tmpDir("lax-site-integrity-commit-");
    expect(() => writeIntegrityManifest(root, "main", "b".repeat(40))).toThrow("website commit");
  });
});
