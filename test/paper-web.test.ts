import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { extractBundleTar } from "../src/bundles.js";
import { loadSubmissions, submissionsMissingPapers } from "../src/database.js";
import { SITE_MIME } from "../src/sitegen/assets.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { EMBED_BUDGET_BYTES } from "../src/sitegen/paper-web.js";
import type { PaperWebEntry } from "../src/types.js";
import { makeTar } from "./tar-helper.js";
import { tmpDir } from "./helpers.js";

import { attach, FIXTURE_TAR, fixtureRecord, pdf, pdfDigest, webArchive } from "./paper-web-archive.js";

/** The real wire schema, so synthetic bundles pass the schema gate. */
const fixtureSchema = extractBundleTar(fs.readFileSync(FIXTURE_TAR)).get("schema/latex.proto")!;

const sha256 = (bytes: Buffer) => createHash("sha256").update(bytes).digest("hex");

function snapshot(root: string, dir = ""): Map<string, Buffer> {
  const out = new Map<string, Buffer>();
  for (const entry of fs.readdirSync(path.join(root, dir), { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
    const relative = path.join(dir, entry.name);
    if (entry.isDirectory()) for (const [name, bytes] of snapshot(root, relative)) out.set(name, bytes);
    else out.set(relative, fs.readFileSync(path.join(root, relative)));
  }
  return out;
}

const csp = (html: string) => /content="([^"]*)"/.exec(html.slice(html.indexOf("Content-Security-Policy")))![1]!;

describe("the reflow paper page", () => {
  it("renders the reflow surface from the committed bundle, embedded under the budget, CSP unchanged", async () => {
    const root = tmpDir("lax-site-reflow-");
    const logs: string[] = [];
    await generateSite(attach(webArchive(), { bundle: FIXTURE_TAR }), root, { log: (line) => logs.push(line) });
    expect(logs).toEqual([]);
    const html = fs.readFileSync(path.join(root, "lax-21", "paper.html"), "utf8");

    // The two surfaces: the paper as printed is the one the page opens on,
    // annotated in its own right — its own rail of cards, under their own
    // ids, and the mark table its script reads — with the reflow surface
    // behind the toggle, its blocks inline (the fixture sits far under the
    // embed budget) and laid out hidden until the reader asks for it.
    expect(html).toContain('<div class="manuscript-body manuscript-reflow-body" id="manuscript-reflow" hidden>');
    expect(html).toContain('<div class="manuscript-pdf" id="manuscript-pdf">');
    expect(html).not.toContain("data-pdf-deferred");
    expect(html).toMatch(/<div class="latex-block" data-nodelist-b64="[A-Za-z0-9+/=]+"><\/div>/);
    expect(html).not.toContain("data-nodelist-src");
    expect(html).toContain('<ol class="manuscript-rail" id="manuscript-rail">\n<li class="manuscript-card');
    expect(html).toContain('"marks":[{"n":1');
    // One card per mark on each surface, the reflow set beside the passages
    // and the printed set beside the pages; the `m<n>` ids stay the text's.
    for (const mark of fixtureRecord.marks) {
      expect(html).toContain(`id="m${mark.n}-card" data-mark="${mark.n}"`);
      expect(html).toContain(`id="m${mark.n}-pdf-card" data-mark="${mark.n}"`);
      expect(html).not.toContain(`<li class="manuscript-card kind-${mark.kind}" id="m${mark.n}"`);
    }
    // The printed view is first in the switch and pressed; the reflowed one
    // is the option beside it.
    expect(html).toContain('<button type="button" class="manuscript-view-button" data-view="pdf" aria-pressed="true">As printed</button>');
    expect(html).toContain('<button type="button" class="manuscript-view-button" data-view="reflow" aria-pressed="false">Reflowed</button>');

    // The islands: the wire schema and the font map, fonts through ../fonts/.
    const schemaB64 = /data-schema-b64="([A-Za-z0-9+/=]+)"/.exec(html)![1]!;
    expect(sha256(Buffer.from(schemaB64, "base64"))).toBe(fixtureRecord.web.format.schema);
    const island = /<script type="application\/json" id="latex-font-map" data-fonts-base="\.\.\/fonts\/">(.*?)<\/script>/.exec(html)![1]!;
    const fontMap = JSON.parse(island) as Record<string, string>;
    expect(Object.keys(fontMap)).toHaveLength(9);
    // Served names are content-hashed uniformly; the converter's own rename
    // is folded away rather than double-suffixed.
    expect(fontMap["lmroman10-regular.otf"]).toMatch(/^lmroman10-regular\.[0-9a-f]{12}\.otf$/);
    expect(fontMap["cmmi10.reflowtex-76a9a304.otf"]).toMatch(/^cmmi10\.[0-9a-f]{12}\.otf$/);
    for (const served of Object.values(fontMap))
      expect(fs.existsSync(path.join(root, "fonts", served)), served).toBe(true);

    // Cards step aside to m<n>-card and m<n>-pdf-card; the m<n> ids belong
    // to the viewer's passage anchors at runtime, so the page ships none.
    expect(html).not.toMatch(/id="m\d+"[^-]/);

    // The AGPL notice under the reflow surface, linking upstream.
    expect(html).toContain('<footer class="manuscript-reflow-notice">Rendered with <a href="https://github.com/radek-p/reflowtex" rel="license">ReflowTeX</a>');
    expect(html).toContain("AGPL-3.0-or-later");

    // The scripts, in dependency order, and the vendored files beside them.
    expect(html).toMatch(/manuscript-place\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="\.\.\/assets\/reflowtex\/latex-viewer\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="\.\.\/assets\/manuscript-reflow\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="\.\.\/assets\/manuscript\.js\?v=[0-9a-f]{12}"><\/script>/);
    for (const asset of ["reflowtex/latex-viewer.js", "reflowtex/LICENSE.txt", "reflowtex/supported-schemas.json", "manuscript-reflow.js"])
      expect(fs.existsSync(path.join(root, "assets", asset)), asset).toBe(true);
    // The CSP finding, kept fixed: no protobuf.js (its decoder needs
    // 'unsafe-eval'); the viewer's own fixed-schema decoder replaces it.
    expect(fs.existsSync(path.join(root, "assets", "reflowtex", "protobuf.min.js"))).toBe(false);
    expect(html).not.toContain("protobuf");
    // Unminified source, with the provenance header naming the upstream rev.
    const viewer = fs.readFileSync(path.join(root, "assets", "reflowtex", "latex-viewer.js"), "utf8");
    expect(viewer).toContain("36f8365eed25ece1db38e0059bcbba3c250802e1");
    expect(viewer).toContain("AGPL");
    expect(viewer.split("\n").length).toBeGreaterThan(1000);

    // The plan's claim, asserted: the reflow page ships under exactly the
    // CSP the pdf.js paper page already had — no loosening, no new sources.
    const plain = tmpDir("lax-site-plain-");
    const noWeb = attach(webArchive()).map((s) => {
      const { web: _, ...paper } = s.output!.paper!;
      return { ...s, output: { ...s.output!, paper } };
    });
    await generateSite(noWeb, plain, { log: () => {} });
    expect(csp(html)).toBe(csp(fs.readFileSync(path.join(plain, "lax-21", "paper.html"), "utf8")));
  });

  it("drops to the PDF-only page, logged, when the schema is not the vendored viewer's", async () => {
    const root = tmpDir("lax-site-gated-");
    const logs: string[] = [];
    const mutated = {
      ...fixtureRecord.web,
      format: { ...fixtureRecord.web.format, schema: "f".repeat(64) },
    };
    await generateSite(attach(webArchive(mutated), { bundle: FIXTURE_TAR }), root, { log: (line) => logs.push(line) });
    expect(logs).toEqual([
      "lax-21: paper web schema ffffffffffff is not supported by the vendored viewer; rendering the PDF-only page",
    ]);
    const html = fs.readFileSync(path.join(root, "lax-21", "paper.html"), "utf8");
    expect(html).not.toContain("latex-block");
    expect(html).not.toContain("manuscript-reflow");
    expect(html).not.toContain("data-pdf-deferred");
    expect(html).toContain('<ol class="manuscript-rail" id="manuscript-rail">\n<li class="manuscript-card');
    expect(html).toContain('id="m1" data-mark="1"');
    expect(html).toContain('"marks":[{"n":1');
    expect(fs.existsSync(path.join(root, "fonts"))).toBe(false);
  });

  it("keeps the PDF-only page when no bundle is attached (previews, missing cache)", async () => {
    const root = tmpDir("lax-site-nobundle-");
    const logs: string[] = [];
    await generateSite(attach(webArchive()), root, { log: (line) => logs.push(line) });
    expect(logs).toEqual([]);
    const html = fs.readFileSync(path.join(root, "lax-21", "paper.html"), "utf8");
    expect(html).not.toContain("latex-block");
    expect(html).toContain('id="m1" data-mark="1"');
  });

  it("ships oversize blocks as fetched files instead of embedding them", async () => {
    // A synthetic bundle whose one block alone overruns the embed budget;
    // its schema is the real one, so the gate passes.
    const big = Buffer.alloc(Math.ceil(EMBED_BUDGET_BYTES * 3 / 4) + 1024, 7);
    const index = {
      formatVersion: 1, tool: "reflowtex", rev: fixtureRecord.web.format.rev,
      schema: sha256(fixtureSchema), blocks: ["blocks/000.pb"], fonts: {},
    };
    const tar = makeTar([
      { name: "index.json", bytes: Buffer.from(JSON.stringify(index)) },
      { name: "blocks/000.pb", bytes: big },
      { name: "schema/latex.proto", bytes: fixtureSchema },
    ]);
    const bundleFile = path.join(tmpDir("lax-bundle-big-"), "big.tar");
    fs.writeFileSync(bundleFile, tar);
    const web: PaperWebEntry = {
      format: { tool: "reflowtex", rev: index.rev, schema: index.schema },
      bundle: { digest: sha256(tar), bytes: tar.length },
    };
    const root = tmpDir("lax-site-bigblocks-");
    await generateSite(attach(webArchive(web), { bundle: bundleFile }), root, { log: () => {} });
    const html = fs.readFileSync(path.join(root, "lax-21", "paper.html"), "utf8");
    expect(html).toContain('<div class="latex-block" data-nodelist-src="paper-web/000.pb"></div>');
    expect(html).not.toContain("data-nodelist-b64");
    expect(fs.readFileSync(path.join(root, "lax-21", "paper-web", "000.pb")).equals(big)).toBe(true);
  });

  it("content-hashing keeps two records' same-named fonts apart and dedupes identical bytes", async () => {
    const fontA = Buffer.from("OTTO first font bytes");
    const fontB = Buffer.from("OTTO second font bytes");
    const bundleFor = (font: Buffer) => {
      const index = {
        formatVersion: 1, tool: "reflowtex", rev: fixtureRecord.web.format.rev,
        schema: sha256(fixtureSchema), blocks: ["blocks/000.pb"], fonts: { "lmroman10-regular.otf": "fonts/lmroman10-regular.otf", "shared.otf": "fonts/shared.otf" },
      };
      return makeTar([
        { name: "index.json", bytes: Buffer.from(JSON.stringify(index)) },
        { name: "blocks/000.pb", bytes: Buffer.from([0x0a, 0x00]) },
        { name: "fonts/lmroman10-regular.otf", bytes: font },
        { name: "fonts/shared.otf", bytes: Buffer.from("OTTO shared bytes") },
        { name: "schema/latex.proto", bytes: fixtureSchema },
      ]);
    };
    const dir = tmpDir("lax-bundle-fonts-");
    const submissions: SiteSubmission[] = [];
    for (const [id, font] of [["lax-31", fontA], ["lax-32", fontB]] as const) {
      const tar = bundleFor(font);
      const file = path.join(dir, `${id}.tar`);
      fs.writeFileSync(file, tar);
      const [base] = webArchive({
        format: { tool: "reflowtex", rev: fixtureRecord.web.format.rev, schema: sha256(fixtureSchema) },
        bundle: { digest: sha256(tar), bytes: tar.length },
      });
      submissions.push({
        ...attach([base!], { bundle: file })[0]!,
        record: { ...base!.record, id },
        output: { ...base!.output!, id, manifest: { ...base!.output!.manifest, id }, concepts: [], proofs: [], paper: { ...base!.output!.paper!, marks: [] } },
      });
    }
    const root = tmpDir("lax-site-fontclash-");
    await generateSite(submissions, root, { log: () => {} });
    const emitted = fs.readdirSync(path.join(root, "fonts")).sort();
    // Two different lmroman10-regular renames plus ONE shared.otf: no clash,
    // identical bytes deduped to a single content-addressed file.
    expect(emitted).toHaveLength(3);
    expect(emitted.filter((name) => name.startsWith("lmroman10-regular."))).toHaveLength(2);
    expect(emitted.filter((name) => name.startsWith("shared."))).toHaveLength(1);
    const maps = ["lax-31", "lax-32"].map((id) => {
      const html = fs.readFileSync(path.join(root, id, "paper.html"), "utf8");
      return JSON.parse(/id="latex-font-map"[^>]*>(.*?)<\/script>/.exec(html)![1]!) as Record<string, string>;
    });
    expect(maps[0]!["lmroman10-regular.otf"]).not.toBe(maps[1]!["lmroman10-regular.otf"]);
    expect(maps[0]!["shared.otf"]).toBe(maps[1]!["shared.otf"]);
  });

  it("builds byte-identical output twice, every emitted extension carrying a MIME type", async () => {
    const one = tmpDir("lax-site-det-one-");
    const two = tmpDir("lax-site-det-two-");
    await generateSite(attach(webArchive(), { bundle: FIXTURE_TAR }), one, { log: () => {} });
    await generateSite(attach(webArchive(), { bundle: FIXTURE_TAR }), two, { log: () => {} });
    const first = snapshot(one);
    const second = snapshot(two);
    expect([...first.keys()]).toEqual([...second.keys()]);
    for (const [name, bytes] of first) {
      expect(bytes.equals(second.get(name)!), name).toBe(true);
      expect(SITE_MIME[path.extname(name)], `missing MIME for ${name}`).toBeDefined();
    }
    expect([...first.keys()].filter((name) => name.startsWith("fonts" + path.sep))).toHaveLength(9);
  });

  it("round-trips the record's web value through the loader and counts a missing bundle", () => {
    const database = tmpDir("lax-database-web-");
    const papers = tmpDir("lax-papers-");
    const bundles = tmpDir("lax-bundles-");
    const [submission] = webArchive();
    const dir = path.join(database, submission!.record.id);
    fs.mkdirSync(dir);
    fs.writeFileSync(path.join(dir, "record.json"), JSON.stringify(submission!.record));
    const { manifest, abstract, ...rest } = submission!.output!;
    fs.writeFileSync(path.join(dir, "build-output.json"), JSON.stringify({ ...rest, inputs: { manifest, abstract } }));
    fs.writeFileSync(path.join(papers, `${pdfDigest}.pdf`), pdf);

    // The PDF alone is not enough: the declared bundle is missing.
    const missing = loadSubmissions(database, { papersDir: papers, bundlesDir: bundles });
    expect(missing[0]!.output!.paper!.web).toEqual(fixtureRecord.web);
    expect(submissionsMissingPapers(missing).map((s) => s.record.id)).toEqual(["lax-21"]);

    fs.copyFileSync(FIXTURE_TAR, path.join(bundles, `${fixtureRecord.web.bundle.digest}.tar`));
    const loaded = loadSubmissions(database, { papersDir: papers, bundlesDir: bundles });
    expect(submissionsMissingPapers(loaded)).toEqual([]);
    expect(loaded[0]!.bundleFile).toBe(path.join(bundles, `${fixtureRecord.web.bundle.digest}.tar`));
    // Without a bundles cache (previews), nothing attaches and nothing is owed.
    expect(loadSubmissions(database, {})[0]!.bundleFile).toBeUndefined();

    // A corrupt web block fails the load with the record named.
    const broken = JSON.parse(fs.readFileSync(path.join(dir, "build-output.json"), "utf8"));
    broken.paper.web.format.schema = "not-hex";
    fs.writeFileSync(path.join(dir, "build-output.json"), JSON.stringify(broken));
    expect(() => loadSubmissions(database)).toThrow(/lax-21.*web format schema must be a sha256 hex string/);
  });

  it("hard-fails on cache corruption and record/bundle skew rather than serving it", async () => {
    // Cached bytes that do not match the record's digest.
    const wrongBytes = path.join(tmpDir("lax-bundle-corrupt-"), "wrong.tar");
    fs.writeFileSync(wrongBytes, makeTar([{ name: "blocks/000.pb", bytes: Buffer.from("x") }]));
    await expect(generateSite(attach(webArchive(), { bundle: wrongBytes }), tmpDir("lax-site-corrupt-"), { log: () => {} }))
      .rejects.toThrow(/lax-21 cached web bundle does not match its record/);

    // A record pinning the supported schema over a bundle sealed with
    // different index metadata: skew, not a graceful gate.
    const index = {
      formatVersion: 1, tool: "reflowtex", rev: "b".repeat(40),
      schema: sha256(fixtureSchema), blocks: ["blocks/000.pb"], fonts: {},
    };
    const tar = makeTar([
      { name: "index.json", bytes: Buffer.from(JSON.stringify(index)) },
      { name: "blocks/000.pb", bytes: Buffer.from([0x0a, 0x00]) },
      { name: "schema/latex.proto", bytes: fixtureSchema },
    ]);
    const skewFile = path.join(tmpDir("lax-bundle-skew-"), "skew.tar");
    fs.writeFileSync(skewFile, tar);
    const web: PaperWebEntry = {
      format: { tool: "reflowtex", rev: fixtureRecord.web.format.rev, schema: sha256(fixtureSchema) },
      bundle: { digest: sha256(tar), bytes: tar.length },
    };
    await expect(generateSite(attach(webArchive(web), { bundle: skewFile }), tmpDir("lax-site-skew-"), { log: () => {} }))
      .rejects.toThrow(/lax-21 paper web bundle index disagrees/);
  });
});
