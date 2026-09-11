import { createHash } from "node:crypto";
import fs from "node:fs";
import { describe, expect, it } from "vitest";
import { parseLeanReferences } from "../src/lean-references.js";
import { downloadBlob } from "../src/papers.js";
import { fetchReferences, loadReferences, referenceCachePath } from "../src/references.js";
import { SiteModel } from "../src/sitegen/model.js";
import { highlightSource } from "../src/sitegen/highlight.js";
import { sourceLinks } from "../src/sitegen/source-links.js";
import { makeTar, type TarEntry } from "./tar-helper.js";
import { tmpDir } from "./helpers.js";
import { referenceModule as module, referenceSource as source, referenceMetadata as metadata, referenceSubmission as submission } from "./lean-reference-fixture.js";

const sha256 = (bytes: Buffer | string) => createHash("sha256").update(bytes).digest("hex");
const blob = (digest: string) => `ghcr.io/lax-archive/lax-captures@sha256:${digest}`;

function model() {
  const entry = submission();
  const references = entry.sourceReferences!.get(module)!;
  return { entry, references, site: new SiteModel([entry]) };
}

describe("compiler-backed navigation", () => {
  it("links open namespaces and standalone submission namespaces without touching locals or selectors", () => {
    const { entry } = model();
    const suffix = [
      "namespace Lax17",
      "open Fields",
      "open Fields (Packet) Fields.Other",
      "open scoped Fields in",
      "section Example",
      "end Example",
      "open Fields hiding Packet Other",
      "open Fields renaming Packet → Renamed",
      "open",
      "  Fields",
      "  Fields.Other",
      "def localName (Lax17 : Nat) := Lax17",
      'def literal := "open Lax17.Fields"',
      "-- open Lax17.Fields",
      "def quoted := `(open Lax17.Fields)",
      "end Lax17",
      "open _root_.Lax17",
      "open Lax17.Fields.Unknown",
      "open Classical",
    ].join("\n");
    const fullSource = source + suffix;
    entry.output!.concepts[0]!.sourceText = fullSource;
    const links = sourceLinks(new SiteModel([entry]), module, "../../").filter((link) => link.start >= source.length);
    expect(links.map((link) => [fullSource.slice(link.start, link.end), link.href])).toEqual([
      ["Lax17", "../../lax-17/index.html"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields.Other", "../../lax-17/Lax17.Fields.html#L11"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields", "../../lax-17/Lax17.Fields.html"],
      ["Fields.Other", "../../lax-17/Lax17.Fields.html#L11"],
      ["Lax17", "../../lax-17/index.html"],
      ["_root_.Lax17", "../../lax-17/index.html"],
    ]);
  });

  it("links record keys, updates, typed projections, aliases and private declarations", async () => {
    const { site, references } = model();
    const links = sourceLinks(site, module, "../");
    const onLine = (line: number) => links.filter((link) => source.slice(0, link.start).split("\n").length === line)
      .map((link) => ({ text: source.slice(link.start, link.end), target: link.href.split("#")[1] }));
    expect(onLine(14)).toEqual([{ text: "Packet", target: "L4" }, { text: "value", target: "L6" }, { text: "enabled", target: "L8" }]);
    expect(onLine(15).at(-1)).toEqual({ text: "value", target: "L6" });
    expect(onLine(16).at(-1)).toEqual({ text: "value", target: "L6" });
    expect(onLine(17).at(-1)).toEqual({ text: "value", target: "L12" });
    expect(onLine(18)).toEqual([{ text: "Packet.mk", target: "L4" }]);
    expect(onLine(21).at(-1)).toEqual({ text: "value", target: "L6" });
    expect(onLine(24).at(-1)).toEqual({ text: "enabled", target: "L8" });
    expect(onLine(27)).toEqual([{ text: "secret", target: "L26" }]);
    expect(onLine(29)).toEqual([]); // Both occurrences of the local `value`.
    expect(onLine(30)).toEqual([{ text: "value", target: "L28" }]);
    expect(onLine(31).at(-1)).toEqual({ text: "value", target: "L6" }); // Astral binder before the projection.
    expect(onLine(38).at(-1)).toEqual({ text: ".first", target: "L36" });
    for (const reference of references.constants) {
      if (!reference.definition) continue;
      expect(links.some((link) => link.start < reference.definition!.end && link.end > reference.definition!.start)).toBe(false);
    }
    expect(links.every((link) => link.href.startsWith("../lax-17/Lax17.Fields.html#L"))).toBe(true);
    const html = await highlightSource(source, [], new Set(), { links });
    expect(html).not.toContain("<script>");
    expect(html).toContain("&lt;script&gt;");
    expect(html.match(/class="lean-identifier-link"/gu)).toHaveLength(links.length);
    expect(sourceLinks(site, module, "../../")[0]!.href).toMatch(/^\.\.\/\.\.\/lax-17\//u);
  });

  it("uses compiler ownership across modules, with imports and stable statement anchors", () => {
    const { entry, references } = model();
    entry.output!.concepts[0]!.statements = [{ id: `${module}.value`, signature: "value", startLine: 28 }];
    const caller = { ...entry.output!.concepts[0]!, id: "Lax17.Caller", path: "concepts/Lax17/Caller.lean",
      imports: [module], statements: [], sourceText: "import Lax17.Fields\n#check Lax17.Fields.value" };
    entry.output!.concepts.push(caller);
    const key = JSON.stringify({ c: { m: module, n: `${module}.value` } });
    entry.sourceReferences!.set(caller.id, parseLeanReferences(JSON.stringify({ version: 5, module: caller.id, decls: {},
      references: { [key]: { definition: null, usages: [[1, 7, 1, 25]] } } }), caller.id, caller.sourceText));
    const links = sourceLinks(new SiteModel([entry]), caller.id, "../");
    expect(links.map((link) => link.href)).toEqual(["../lax-17/Lax17.Fields.html", "../lax-17/Lax17.Fields.html#s-Lax17.Fields.value"]);
    expect(references.module).toBe(module);
  });

  it("keeps precise names from duplicated universe-application spans and rejects conflicting targets", () => {
    const entry = submission();
    const text = "def T := Type\n#check T.{u}";
    entry.output!.concepts[0]!.sourceText = text;
    const refs = parseLeanReferences(JSON.stringify({ version: 5, module, decls: {}, references: {
      [JSON.stringify({ c: { m: module, n: `${module}.T` } })]: { definition: [0, 4, 0, 5], usages: [[1, 7, 1, 8], [1, 7, 1, 12]] },
    } }), module, text);
    entry.sourceReferences = new Map([[module, refs]]);
    expect(sourceLinks(new SiteModel([entry]), module, "../").map((link) => text.slice(link.start, link.end))).toEqual(["T"]);
    refs.constants.push({ module, name: "unknown", usages: [refs.constants[0]!.usages[0]!] });
    expect(() => sourceLinks(new SiteModel([entry]), module, "../")).toThrow("overlapping");
  });

  it("validates versions, owning modules, bounds, Unicode boundaries and declaration ranges", () => {
    for (let variant = 0; variant < 5; variant++) {
      const parsed = JSON.parse(metadata.toString("utf8"));
      const first = Object.values(parsed.references)[0] as { usages: number[][] };
      if (variant === 0) parsed.version = 99;
      if (variant === 1) parsed.module = "Other";
      if (variant === 2) first.usages = [[9999, 0, 9999, 1]];
      if (variant === 3) first.usages = [[30, 13, 30, 14]]; // Splits 𝒜's surrogate pair.
      if (variant === 4) parsed.decls.bad = [0, 0, 0, 1, 1, 0, 1, 1];
      expect(() => parseLeanReferences(JSON.stringify(parsed), module, source)).toThrow("invalid Lean references");
    }
  });
});

/** Captures sort directory entries before visiting the next sibling. The
 * `Lax17.extra` sibling detects the tempting, incorrect flat-path sort. */
function capture(mutate: (entries: TarEntry[]) => void = () => {}) {
  const entries: TarEntry[] = [
    { name: "./", type: "5" }, { name: "./concepts/", type: "5" },
    { name: "./concepts/lib/", type: "5" }, { name: "./concepts/lib/Lax17/", type: "5" },
    { name: "./concepts/lib/Lax17/Fields.ilean", bytes: metadata },
    { name: "./concepts/lib/Lax17.extra", bytes: Buffer.from("sibling") },
    { name: "./concepts/package/", type: "5" }, { name: "./concepts/package/Lax17/", type: "5" },
    { name: "./concepts/package/Lax17/Fields.lean", bytes: Buffer.from(source) },
    { name: "./proofs/", type: "5" }, { name: "./proofs/unused", bytes: Buffer.alloc(2 * 1024 * 1024) },
  ];
  const files = entries.filter((entry) => entry.bytes).map((entry) => ({ path: entry.name.slice(2), bytes: entry.bytes!.length, sha256: sha256(entry.bytes!) }));
  mutate(entries);
  const tar = makeTar(entries);
  const entry = submission();
  entry.output!.capture = { formatVersion: 1, leanToolchain: "leanprover/lean4:v4.30.0", mathlibCommit: "abc",
    digest: sha256(tar), registryBlob: blob(sha256(tar)), files: files.reverse() };
  return { entry, tar };
}

function registry(tar: Buffer, log: { url: string; auth: string | null; range: string | null }[]): typeof fetch {
  return async (input, init) => {
    const url = String(input);
    const headers = new Headers(init?.headers);
    log.push({ url, auth: headers.get("authorization"), range: headers.get("range") });
    if (url.includes("/token?")) return new Response(JSON.stringify({ token: "anonymous" }));
    if (url.startsWith("https://ghcr.io/"))
      return new Response(null, { status: 307, headers: { location: "https://pkg-containers.githubusercontent.com/capture" } });
    const match = /^bytes=(\d+)-(\d+)$/u.exec(headers.get("range")!)!;
    const start = Number(match[1]), end = Number(match[2]);
    return new Response(tar.subarray(start, end + 1), { status: 206,
      headers: { "content-range": `bytes ${start}-${end}/${tar.length}` } });
  };
}

describe("sealed compiler reference cache", () => {
  it("fetches just the metadata range, verifies cached bytes again, and never extracts paths", async () => {
    const { entry, tar } = capture();
    const directory = tmpDir();
    const log: { url: string; auth: string | null; range: string | null }[] = [];
    expect(await fetchReferences([entry], directory, { fetch: registry(tar, log) })).toEqual([sha256(metadata)]);
    expect(log.map((call) => call.auth)).toEqual([null, "Bearer anonymous", null]);
    expect(log[1]!.range).toBe(log[2]!.range);
    expect(log[2]!.range).toBe(`bytes=2048-${2048 + 512 + metadata.length - 1}`);
    expect(fs.readdirSync(directory)).toEqual([`${sha256(metadata)}.ilean`]);
    expect(loadReferences(entry, directory)!.get(module)!.constants.length).toBeGreaterThan(10);
    expect(await fetchReferences([entry], directory, { fetch: () => { throw new Error("unexpected network"); } })).toEqual([]);
    fs.writeFileSync(referenceCachePath(directory, sha256(metadata)), Buffer.alloc(metadata.length));
    expect(() => loadReferences(entry, directory)).toThrow("digest mismatch");
  });

  it("fails closed on mismatched source, missing metadata, unsafe manifests and wrong tar members", async () => {
    const { entry } = capture();
    const directory = tmpDir();
    expect(() => loadReferences(entry, directory)).toThrow("references:fetch");
    entry.output!.concepts[0]!.sourceText += " ";
    expect(() => loadReferences(entry, directory)).toThrow("does not match displayed source");
    expect(() => referenceCachePath(directory, "../escape")).toThrow("sha256");
    for (const mutate of [
      (entries: TarEntry[]) => { entries[4]!.corruptChecksum = true; },
      (entries: TarEntry[]) => { entries[4]!.type = "2"; },
      (entries: TarEntry[]) => { entries[4]!.name = "./wrong.ilean"; },
      (entries: TarEntry[]) => { entries[4]!.bytes = Buffer.alloc(metadata.length); },
    ]) {
      const fixture = capture(mutate);
      await expect(fetchReferences([fixture.entry], tmpDir(), { fetch: registry(fixture.tar, []) })).rejects.toThrow(/header|digest/u);
    }
    for (const name of ["../escape", "/absolute", "a\\b", "a//b", "a/./b"]) {
      const fixture = capture();
      fixture.entry.output!.capture!.files![0]!.path = name;
      await expect(fetchReferences([fixture.entry], tmpDir())).rejects.toThrow("capture member");
    }
  });

  it("rejects ignored, wrong, truncated and overlong ranges before storing metadata", async () => {
    const address = blob("a".repeat(64));
    for (const response of [
      new Response("a", { status: 200 }),
      new Response("ab", { status: 206, headers: { "content-range": "bytes 1-2/10" } }),
      new Response("a", { status: 206, headers: { "content-range": "bytes 0-1/10" } }),
      new Response("abc", { status: 206, headers: { "content-range": "bytes 0-1/10" } }),
    ]) {
      const transport: typeof fetch = async (input) => String(input).includes("/token?")
        ? new Response(JSON.stringify({ token: "anonymous" })) : response;
      await expect(downloadBlob(address, transport, { start: 0, end: 1 })).rejects.toThrow(/range|exceeds/u);
    }
    for (const location of ["http://ghcr.io/blob", "https://ghcr.io:8443/blob", "https://user@ghcr.io/blob", "https://evil.test/blob"]) {
      const transport: typeof fetch = async (input) => String(input).includes("/token?")
        ? new Response(JSON.stringify({ token: "anonymous" }))
        : new Response(null, { status: 307, headers: { location } });
      await expect(downloadBlob(address, transport, { start: 0, end: 1 })).rejects.toThrow("allowed public HTTPS");
    }
  });
});
