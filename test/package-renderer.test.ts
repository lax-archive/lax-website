import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  packageRenderer,
  verifyRendererArchive,
} from "../.github/scripts/package-renderer.mjs";
import { tmpDir } from "./helpers.js";

const commit = "0123456789abcdef0123456789abcdef01234567";

describe("Pages renderer package", () => {
  it("packs the CLI runtime contract and reuses an artifact for the same commit", () => {
    const repository = rendererFixture();
    const output = tmpDir("lax-renderer-output-");

    const first = packageRenderer(commit, output, repository);
    expect(first.reused).toBe(false);
    expect(path.basename(first.archive)).toBe(`${commit}.tgz`);
    expect(first.sha256).toMatch(/^[0-9a-f]{64}$/u);
    expect(() => verifyRendererArchive(first.archive)).not.toThrow();
    expect(JSON.parse(fs.readFileSync(path.join(output, "latest.json"), "utf8"))).toEqual({
      commit,
      tarball: `${commit}.tgz`,
      sha256: first.sha256,
    });

    fs.writeFileSync(path.join(repository, "content", "landing.md"), "changed after packing");
    const second = packageRenderer(commit, output, repository);
    expect(second).toMatchObject({ reused: true, sha256: first.sha256 });
    expect(fs.readdirSync(output).sort()).toEqual([`${commit}.tgz`, "latest.json"]);
  });

  it("rejects a package that omits a required renderer file", () => {
    const repository = rendererFixture();
    fs.rmSync(path.join(repository, "dist", "sitegen", "assets.js"));
    const output = tmpDir("lax-renderer-output-");

    expect(() => packageRenderer(commit, output, repository)).toThrow(
      "renderer archive is missing dist/sitegen/assets.js",
    );
    expect(fs.existsSync(path.join(output, `${commit}.tgz`))).toBe(false);
  });
});

function rendererFixture(): string {
  const root = tmpDir("lax-renderer-fixture-");
  const files: Record<string, string> = {
    "assets/site/style.css": "body {}\n",
    "content/contributing.md": "Contributing\n",
    "content/landing.md": "Landing\n",
    "dist/sitegen/assets.js": "export const SITE_MIME = {};\n",
    "dist/sitegen/generate.js": "export async function generateSite() {}\n",
    "dist/sitegen/machine-index.js": "export function machineIndex() {}\n",
  };
  for (const [relative, contents] of Object.entries(files)) {
    const filename = path.join(root, relative);
    fs.mkdirSync(path.dirname(filename), { recursive: true });
    fs.writeFileSync(filename, contents);
  }
  fs.writeFileSync(
    path.join(root, "package.json"),
    `${JSON.stringify({
      name: "lax-renderer-test-fixture",
      version: "1.0.0",
      private: true,
      files: ["assets", "content", "dist"],
    }, null, 2)}\n`,
  );
  return root;
}
