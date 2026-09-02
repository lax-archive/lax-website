import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  bundleCachePath,
  bundleReferences,
  extractBundleTar,
  fetchBundles,
  MAX_BUNDLE_BYTES,
  readPaperBundle,
} from "../src/bundles.js";
import type { SiteSubmission } from "../src/sitegen/model.js";
import { makeTar } from "./tar-helper.js";
import { tmpDir } from "./helpers.js";

const FIXTURE_TAR = path.join("test", "fixtures", "paper-web", "paper-web.tar");
const FIXTURE_RECORD = path.join("test", "fixtures", "paper-web", "paper-web.json");

const sha256 = (bytes: Buffer) => createHash("sha256").update(bytes).digest("hex");

/** The smallest valid bundle: a schema, one block, no fonts. */
function tinyBundle(mutate: (index: Record<string, unknown>) => void = () => {}): Buffer {
  const schema = Buffer.from("syntax = \"proto2\";\n");
  const block = Buffer.from([0x0a, 0x00]);
  const index: Record<string, unknown> = {
    formatVersion: 1,
    tool: "reflowtex",
    rev: "a".repeat(40),
    schema: sha256(schema),
    blocks: ["blocks/000.pb"],
    fonts: {},
  };
  mutate(index);
  return makeTar([
    { name: "index.json", bytes: Buffer.from(JSON.stringify(index)) },
    { name: "blocks/000.pb", bytes: block },
    { name: "schema/latex.proto", bytes: schema },
  ]);
}

function submissionWithBundle(id: string, digest: string, bytes: number, registryBlob?: string): SiteSubmission {
  return {
    record: { specVersion: "1", id, state: "registered", createdAt: "2026-09-01T00:00:00Z" },
    output: {
      specVersion: "1", id,
      manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: id, authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [], concepts: [], proofs: [],
      paper: {
        folder: "paper", main: "main.tex", engine: "lualatex",
        pdf: { digest: "b".repeat(64), bytes: 10, pages: 1 },
        pageSizes: [[595.28, 841.89]], marks: [],
        web: {
          format: { tool: "reflowtex", rev: "a".repeat(40), schema: "c".repeat(64) },
          bundle: { digest, bytes, ...(registryBlob === undefined ? {} : { registryBlob }) },
        },
      },
    },
  };
}

describe("the bundles cache", () => {
  it("names cache files by digest and lists each referenced bundle once", () => {
    const digest = "d".repeat(64);
    expect(bundleCachePath("/cache", digest)).toBe(path.join("/cache", `${digest}.tar`));
    expect(() => bundleCachePath("/cache", "../escape")).toThrow("not sha256 hex");
    const blob = `ghcr.io/lax-archive/lax-captures@sha256:${digest}`;
    const references = bundleReferences([
      submissionWithBundle("lax-2", digest, 1, blob),
      submissionWithBundle("lax-3", digest, 1, blob),
    ]);
    expect(references).toEqual([{ submissionId: "lax-2", digest, registryBlob: blob }]);
    expect(() => bundleReferences([submissionWithBundle("lax-9", digest, 1)]))
      .toThrow("without a registry blob");
    expect(() => bundleReferences([submissionWithBundle("lax-9", digest, 1, `ghcr.io/lax-archive/lax-captures@sha256:${"0".repeat(64)}`)]))
      .toThrow("not a ghcr address of its digest");
  });

  it("downloads missing bundles anonymously, verifies digest and shape, and skips cached ones", async () => {
    const tar = tinyBundle();
    const digest = sha256(tar);
    const blob = `ghcr.io/lax-archive/lax-captures@sha256:${digest}`;
    const submissions = [submissionWithBundle("lax-2", digest, tar.length, blob)];
    const log: string[] = [];
    const registry: typeof fetch = async (input, init) => {
      const url = String(input);
      log.push(`${url} ${new Headers(init?.headers).get("authorization") ?? ""}`.trim());
      if (url.startsWith("https://ghcr.io/token?")) return new Response(JSON.stringify({ token: "anon" }), { status: 200 });
      if (url.startsWith("https://ghcr.io/v2/")) return new Response(tar, { status: 200, headers: { "content-length": String(tar.length) } });
      return new Response("nope", { status: 404 });
    };
    const cache = tmpDir("lax-bundles-");
    expect(await fetchBundles(submissions, cache, { fetch: registry })).toEqual([digest]);
    expect(fs.readFileSync(bundleCachePath(cache, digest))).toEqual(tar);
    expect(await fetchBundles(submissions, cache, { fetch: registry })).toEqual([]);

    const wrong = submissionWithBundle("lax-2", "e".repeat(64), tar.length, `ghcr.io/lax-archive/lax-captures@sha256:${"e".repeat(64)}`);
    await expect(fetchBundles([wrong], tmpDir("lax-bundles-bad-"), { fetch: registry })).rejects.toThrow("downloaded with digest");
    const text = Buffer.from("not a tar at all, but padded to a full block".padEnd(512, "."));
    const textDigest = sha256(text);
    const textRegistry: typeof fetch = async (input) => {
      const url = String(input);
      if (url.includes("/token?")) return new Response(JSON.stringify({ token: "anon" }), { status: 200 });
      return new Response(text, { status: 200 });
    };
    await expect(fetchBundles(
      [submissionWithBundle("lax-2", textDigest, text.length, `ghcr.io/lax-archive/lax-captures@sha256:${textDigest}`)],
      tmpDir("lax-bundles-bad-"),
      { fetch: textRegistry },
    )).rejects.toThrow("is not a ustar archive");
  });
});

describe("the bounded extractor", () => {
  it("extracts the committed fixture bundle exactly", () => {
    const tar = fs.readFileSync(FIXTURE_TAR);
    const record = JSON.parse(fs.readFileSync(FIXTURE_RECORD, "utf8")) as { web: { bundle: { digest: string; bytes: number } } };
    expect(sha256(tar)).toBe(record.web.bundle.digest);
    expect(tar.length).toBe(record.web.bundle.bytes);
    const files = extractBundleTar(tar);
    expect([...files.keys()].sort()).toEqual([
      "blocks/000.pb",
      "fonts/cmmi10.reflowtex-76a9a304.otf",
      "fonts/cmr10.reflowtex-0af15112.otf",
      "fonts/cmsy10.reflowtex-1ccf252d.otf",
      "fonts/lmroman10-bold.otf",
      "fonts/lmroman10-italic.otf",
      "fonts/lmroman10-regular.otf",
      "fonts/lmroman12-bold.otf",
      "fonts/lmroman12-regular.otf",
      "fonts/lmroman17-regular.otf",
      "index.json",
      "schema/latex.proto",
    ]);
    const bundle = readPaperBundle(tar);
    expect(bundle.index.formatVersion).toBe(1);
    expect(bundle.index.tool).toBe("reflowtex");
    expect(bundle.index.blocks).toEqual(["blocks/000.pb"]);
    expect(Object.keys(bundle.index.fonts)).toHaveLength(9);
    expect(sha256(bundle.files.get("schema/latex.proto")!)).toBe(bundle.index.schema);
  });

  it("refuses links, directories, pax members, and anything off the allowlist", () => {
    const pb = Buffer.from("x");
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", type: "2", bytes: Buffer.alloc(0) }])))
      .toThrow("not a regular file");
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", type: "1", bytes: Buffer.alloc(0) }])))
      .toThrow("not a regular file");
    expect(() => extractBundleTar(makeTar([{ name: "fonts/", type: "5" }, { name: "blocks/000.pb", bytes: pb }])))
      .toThrow("not a regular file");
    expect(() => extractBundleTar(makeTar([{ name: "pax", type: "x", bytes: Buffer.from("path=evil") }])))
      .toThrow("not a regular file");
    for (const name of ["../evil.pb", "fonts/../index.json", "/etc/passwd", "evil.txt", "blocks/0000.pb", "fonts/.hidden.otf", "fonts/deep/font.otf", "schema/other.proto"])
      expect(() => extractBundleTar(makeTar([{ name, bytes: pb }])), name).toThrow("disallowed name");
    expect(() => extractBundleTar(makeTar([{ name: "x.otf", prefix: "fonts", bytes: pb }])))
      .toThrow(/prefix field|disallowed name/);
  });

  it("enforces the caps, the checksums, and clean framing", () => {
    const pb = Buffer.from("x");
    // A member claiming more than the per-file cap is refused unread.
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", claimSize: 21 * 1024 * 1024 }])))
      .toThrow("exceeds");
    // Members that together pass the whole-bundle cap.
    expect(() => extractBundleTar(makeTar([
      { name: "blocks/000.pb", claimSize: 13 * 1024 * 1024 },
      { name: "blocks/001.pb", claimSize: 13 * 1024 * 1024 },
    ]))).toThrow(/together|truncated/);
    // An entry-count bomb of tiny allowlisted names.
    const many = Array.from({ length: 513 }, (_, i) => ({ name: `fonts/f${String(i).padStart(3, "0")}.otf`, bytes: pb }));
    expect(() => extractBundleTar(makeTar(many))).toThrow("entries");
    // Duplicates, corrupt checksums, truncation, junk after the terminator.
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", bytes: pb }, { name: "blocks/000.pb", bytes: pb }])))
      .toThrow("repeats");
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", bytes: pb, corruptChecksum: true }])))
      .toThrow("checksum");
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", claimSize: 100_000 }])))
      .toThrow("truncated");
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", bytes: pb, magic: "gnu\0\0" }])))
      .toThrow("not ustar");
    const withJunk = Buffer.concat([makeTar([{ name: "blocks/000.pb", bytes: pb }]), Buffer.alloc(512, 0xff)]);
    expect(() => extractBundleTar(withJunk)).toThrow("after its terminator");
    expect(() => extractBundleTar(Buffer.from("short"))).toThrow("not block-aligned");
    expect(() => extractBundleTar(Buffer.alloc(MAX_BUNDLE_BYTES + 512))).toThrow("exceeds");
    // A stream that ends without the zero terminator.
    expect(() => extractBundleTar(makeTar([{ name: "blocks/000.pb", bytes: pb }]).subarray(0, 1024))).toThrow("terminator");
  });

  it("cross-checks the index against the members and the schema hash", () => {
    expect(() => readPaperBundle(tinyBundle())).not.toThrow();
    expect(() => readPaperBundle(makeTar([{ name: "blocks/000.pb", bytes: Buffer.from("x") }])))
      .toThrow("no index.json");
    expect(() => readPaperBundle(tinyBundle((index) => { index.blocks = ["blocks/001.pb"]; })))
      .toThrow("missing block");
    expect(() => readPaperBundle(tinyBundle((index) => { index.blocks = []; })))
      .toThrow("non-empty");
    expect(() => readPaperBundle(tinyBundle((index) => { index.schema = "0".repeat(64); })))
      .toThrow("index says");
    expect(() => readPaperBundle(tinyBundle((index) => { index.fonts = { "a.otf": "fonts/missing.otf" }; })))
      .toThrow("missing font");
    // A member the index never references is refused too.
    const schema = Buffer.from("syntax = \"proto2\";\n");
    const orphan = makeTar([
      { name: "index.json", bytes: Buffer.from(JSON.stringify({ formatVersion: 1, tool: "reflowtex", rev: "a".repeat(40), schema: sha256(schema), blocks: ["blocks/000.pb"], fonts: {} })) },
      { name: "blocks/000.pb", bytes: Buffer.from("x") },
      { name: "blocks/001.pb", bytes: Buffer.from("y") },
      { name: "schema/latex.proto", bytes: schema },
    ]);
    expect(() => readPaperBundle(orphan)).toThrow("does not reference");
  });
});
