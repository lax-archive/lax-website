import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { ENVIRONMENT_SPEC_VERSIONS, environmentSpecVersion } from "../src/config.js";
import { derivedEdge, loadSubmissions, rendererOutput } from "../src/database.js";
import { fetchReferences, loadReferences, referenceLayerPath } from "../src/references.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { environmentIndex } from "../src/sitegen/machine-index.js";
import { isCertified, SiteModel } from "../src/sitegen/model.js";
import type { BuildOutput } from "../src/types.js";
import { tmpDir } from "./helpers.js";
import { makeTar, type TarEntry } from "./tar-helper.js";

const FIXTURE = path.resolve("test/fixtures/spec2");
const sha256 = (bytes: Buffer | string) => createHash("sha256").update(bytes).digest("hex");
const blob = (digest: string) => `ghcr.io/lax-archive/lax-captures@sha256:${digest}`;

/** The stored spec-2 record, as `lax-database` holds it. */
function storedRecord(): Record<string, any> {
  return JSON.parse(fs.readFileSync(path.join(FIXTURE, "lax-38", "build-output.json"), "utf8"));
}

/** A database directory holding the spec-2 fixture beside a spec-1 record
 * that depends on nothing — the two shapes side by side, as the archive
 * will hold them until the port finishes. */
function database(extra: (root: string) => void = () => {}): string {
  const root = tmpDir("lax-spec2-db-");
  fs.cpSync(FIXTURE, root, { recursive: true });
  fs.rmSync(path.join(root, "README.md"), { force: true });
  fs.mkdirSync(path.join(root, "lax-2"));
  fs.writeFileSync(path.join(root, "lax-2", "record.json"), JSON.stringify({
    specVersion: "1", id: "lax-2", state: "registered", createdAt: "2026-01-01T00:00:00Z", registeredAt: "2026-01-02T00:00:00Z",
  }));
  fs.writeFileSync(path.join(root, "lax-2", "build-output.json"), JSON.stringify({
    specVersion: "1", id: "lax-2",
    inputs: {
      manifest: { specVersion: "1", id: "lax-2", leanVersion: "v4.33.0", mathlibVersion: "c".repeat(40), title: "Two", authors: [], bibEntries: [] },
      abstract: "A spec-1 record.",
    },
    requiredByConcepts: [], requiredByProofs: [],
    concepts: [{
      id: "Lax2.C", path: "concepts/Lax2/C.lean", title: "Truth", type: "theorem", description: "d", imports: [], mathlibImports: [],
      sourceText: "namespace Lax2.C\naxiom truth : True\nend Lax2.C\n",
      statements: [{ id: "Lax2.C.truth", signature: "truth : True", startLine: 2, endLine: 2 }],
    }],
    proofs: [{ id: "Lax2Proofs.truth", path: "proofs/Lax2Proofs/Basic.lean", conclusion: "Lax2.C.truth", assumptions: [], description: "Direct." }],
  }));
  extra(root);
  return root;
}

/** A sealed `references` layer for the fixture's one concept: its source and
 * a minimal version-5 `.ilean`, as plain ustar in 10240-byte records. */
function layer(sourceText: string, mutate: (entries: TarEntry[]) => void = () => {}): { tar: Buffer; digest: string } {
  const ilean = Buffer.from(JSON.stringify({ version: 5, module: "Lax38.Order", decls: {}, references: {} }));
  const entries: TarEntry[] = [
    { name: "./concepts/lib/Lax38/Order.ilean", bytes: ilean },
    { name: "./concepts/package/Lax38/Order.lean", bytes: Buffer.from(sourceText) },
  ];
  mutate(entries);
  const unblocked = makeTar(entries);
  const tar = Buffer.concat([unblocked, Buffer.alloc((10_240 - (unblocked.length % 10_240)) % 10_240)]);
  return { tar, digest: sha256(tar) };
}

/** A registry answering the anonymous token and the whole blob by digest. */
function registry(blobs: Map<string, Buffer>, log: string[] = []): typeof fetch {
  return async (input, init) => {
    const url = String(input);
    log.push(url);
    if (new Headers(init?.headers).get("range") !== null) throw new Error("a layer is fetched whole, never by range");
    if (url.includes("/token?")) return new Response(JSON.stringify({ token: "anonymous" }));
    const digest = /sha256:([0-9a-f]{64})$/u.exec(url)?.[1];
    const bytes = digest === undefined ? undefined : blobs.get(digest);
    return bytes ? new Response(bytes, { status: 200 }) : new Response(null, { status: 404 });
  };
}

describe("spec-2 records in the loader", () => {
  it("expands a stored spec-2 record into the renderer's one shape", () => {
    const stored = storedRecord();
    expect(stored.inputs.manifest.id).toBeUndefined();
    expect(stored.proofs[1].conclusion).toBeUndefined();
    expect(stored.capture.files).toBeUndefined();

    const output = rendererOutput(stored, "lax-38/build-output.json", "lax-38")!;
    expect(output.manifest.id).toBe("lax-38");
    expect(output.manifest.specVersion).toBe("2");
    // the derivation: the conclusion constant, the hypotheses as a sorted set
    expect(output.proofs.map((proof) => [proof.conclusion, proof.assumptions])).toEqual([
      ["Lax38.Order.HasSucc", []],
      ["Lax38.Order.Refl", ["Lax38.Order.HasSucc"]],
    ]);
    expect(output.proofs[1]!.telescope!.hypotheses).toEqual([
      { statement: "Lax38.Order.HasSucc", levels: [] }, { statement: "Lax38.Order.HasSucc", levels: [] },
    ]);
    expect(output.proofs[1]!.levelParams).toEqual(["u"]);
    expect(output.capture!.references).toEqual({ digest: "2".repeat(64), bytes: 10_240, registryBlob: blob("2".repeat(64)) });
    expect(output.capture!.leanToolchain).toBeUndefined();
    expect(output.certificate).not.toHaveProperty("judge");
    expect(output.certificate!.kernels).toEqual(["lean"]);
    expect(output.certificate!.challenge).toContain("theorem Lax38Proofs.refl_of_hasSucc.{u}");
    expect(output.certificate!.challengeExportSha256).toBe("4".repeat(64));
    expect(output.certificate!.solutionExportSha256).toBe("7".repeat(64));
    expect(output.concepts[0]!.statements[0]!.body).toBe("∀ (n : Nat), Exists fun m => n < m");
    expect(derivedEdge({ hypotheses: [
      { statement: "B", levels: [] }, { statement: "A", levels: [] }, { statement: "B", levels: [] },
    ], conclusion: { statement: "C", levels: [] } })).toEqual({ conclusion: "C", assumptions: ["A", "B"] });
  });

  it("reads a spec-2 paper block's folder, main and engine from the manifest", () => {
    const stored = storedRecord();
    stored.inputs.manifest.paper = { folder: "paper", main: "main.tex", engine: "lualatex" };
    stored.paper = {
      pdf: { digest: "a".repeat(64), bytes: 1, pages: 1, registryBlob: blob("a".repeat(64)) },
      pageSizes: [[612, 792]], marks: [],
    };
    const output = rendererOutput(stored, "x", "lax-38")!;
    expect(output.paper).toMatchObject({ folder: "paper", main: "main.tex", engine: "lualatex", pdf: { pages: 1 } });
    delete stored.inputs.manifest.paper;
    expect(() => rendererOutput(stored, "x", "lax-38")).toThrow("declares no paper");
  });

  it("names a malformed telescope, certificate, or references layer", () => {
    const broken = (mutate: (stored: Record<string, any>) => void) => {
      const stored = storedRecord();
      mutate(stored);
      return () => rendererOutput(stored, "x", "lax-38");
    };
    expect(broken((s) => { delete s.proofs[0].telescope; })).toThrow("proof 1 telescope must be an object");
    expect(broken((s) => { s.proofs[1].telescope.hypotheses[0].statement = "not a name!"; })).toThrow("hypothesis 1 statement must be a Lean name");
    expect(broken((s) => { s.proofs[1].telescope.conclusion.statement = "not a name!"; })).toThrow("conclusion statement must be a Lean name");
    // the archive's grammar (lax contracts.ts LEAN_NAME_PATTERN): what Lean
    // prints with «» is no archive name, Lean's other identifier characters are
    expect(broken((s) => { s.proofs[1].telescope.hypotheses[0].statement = "Lax38.Order.«定理»"; })).toThrow("hypothesis 1 statement must be a Lean name");
    expect(broken((s) => { s.proofs[1].telescope.hypotheses[0].statement = "Lax38.Order.λ"; })).toThrow("hypothesis 1 statement must be a Lean name");
    expect(broken((s) => { s.proofs[1].telescope.hypotheses[0].statement = "Lax38.Order.good?"; })).not.toThrow("must be a Lean name");
    expect(broken((s) => { s.certificate.kernels = []; })).toThrow("kernels must name at least one kernel");
    expect(broken((s) => { s.certificate.challenge = ""; })).toThrow("challenge must be the Challenge.lean source");
    expect(broken((s) => { s.certificate.bundle.registryBlob = blob("9".repeat(64)); })).toThrow("bundle registryBlob is not a ghcr address of its digest");
    expect(broken((s) => { s.certificate.solutionExportSha256 = "not-hex"; })).toThrow("solutionExportSha256 must be a sha256 hex string");
    expect(broken((s) => { delete s.certificate.solutionExportSha256; })).toThrow("solutionExportSha256 must be a sha256 hex string");
    expect(broken((s) => { delete s.certificate; })).toThrow("certificate is missing on a record with a complete proof");
    expect(broken((s) => { s.proofs = []; })).toThrow("certificate is present on a record without a complete proof");
    // pending edges (lax decision 12): only `true`, and the certificate keys
    // on the complete proofs alone
    expect(broken((s) => { s.proofs[1].pending = false; })).toThrow("proof 2 pending must be true when present");
    expect(broken((s) => { s.proofs[1].pending = true; })).not.toThrow();
    expect(broken((s) => { s.proofs[1].pending = true; delete s.certificate; })).toThrow("certificate is missing on a record with a complete proof");
    expect(broken((s) => { for (const proof of s.proofs) proof.pending = true; })).toThrow("certificate is present on a record without a complete proof");
    expect(broken((s) => { for (const proof of s.proofs) proof.pending = true; delete s.certificate; })).not.toThrow();
    expect(broken((s) => { s.capture.references.registryBlob = blob("9".repeat(64)); })).toThrow("references registryBlob is not a ghcr address of its digest");
    expect(broken((s) => { s.inputs.manifest.id = "lax-99"; })).toThrow('manifest names "lax-99", not lax-38');
  });

  it("loads both shapes from one database and skips a spec-2 record that fails its checks", () => {
    const root = database((dir) => {
      fs.mkdirSync(path.join(dir, "lax-40"));
      fs.writeFileSync(path.join(dir, "lax-40", "record.json"), JSON.stringify({ specVersion: "1", id: "lax-40", state: "draft", createdAt: "2026-10-03T00:00:00Z" }));
      const stored = storedRecord();
      stored.proofs[0].telescope = "no";
      fs.writeFileSync(path.join(dir, "lax-40", "build-output.json"), JSON.stringify(stored));
    });
    const skipped: Array<{ id: string; reason: string }> = [];
    const submissions = loadSubmissions(root, { onSkip: (skip) => skipped.push(skip) });
    expect(submissions.map((submission) => submission.record.id)).toEqual(["lax-2", "lax-38"]);
    expect(skipped).toEqual([{ id: "lax-40", reason: expect.stringContaining("proof 1 telescope must be an object") }]);
    expect(submissions[1]!.output!.proofs[1]!.assumptions).toEqual(["Lax38.Order.HasSucc"]);
    expect(submissions[0]!.output!.proofs[0]!.telescope).toBeUndefined();
  });
});

describe("the references layer of a spec-2 record", () => {
  it("downloads the layer whole, verifies it by digest, caches it, and reads references from it", async () => {
    const root = database();
    const [, submission] = loadSubmissions(root);
    const concept = submission!.output!.concepts[0]!;
    const sealed = layer(concept.sourceText);
    submission!.output!.capture!.references = { digest: sealed.digest, bytes: sealed.tar.length, registryBlob: blob(sealed.digest) };
    const directory = tmpDir("lax-spec2-references-");
    const log: string[] = [];

    expect(() => loadReferences(submission!, directory)).toThrow("references:fetch");
    expect(await fetchReferences([submission!], directory, { fetch: registry(new Map([[sealed.digest, sealed.tar]]), log) })).toEqual([sealed.digest]);
    expect(log).toHaveLength(2); // the token, then the blob — nothing else
    expect(fs.readdirSync(directory)).toEqual([`${sealed.digest}.references.tar`]);
    expect(fs.readFileSync(referenceLayerPath(directory, sealed.digest)).equals(sealed.tar)).toBe(true);
    const references = loadReferences(submission!, directory)!;
    expect(references.get(concept.id)!.module).toBe("Lax38.Order");
    // cached: no network at all
    expect(await fetchReferences([submission!], directory, { fetch: () => { throw new Error("unexpected network"); } })).toEqual([]);
    // the cache is verified again on every read
    fs.writeFileSync(referenceLayerPath(directory, sealed.digest), Buffer.alloc(sealed.tar.length));
    expect(() => loadReferences(submission!, directory)).toThrow("does not match its recorded digest");
  });

  it("fails closed on a tampered, misnamed, or source-mismatched layer", async () => {
    const root = database();
    const [, submission] = loadSubmissions(root);
    const concept = submission!.output!.concepts[0]!;
    const declare = (sealed: { tar: Buffer; digest: string }, digest = sealed.digest) => {
      submission!.output!.capture!.references = { digest, bytes: sealed.tar.length, registryBlob: blob(digest) };
    };
    // tampered bytes behind the right address
    const good = layer(concept.sourceText);
    declare(good);
    const tampered = Buffer.from(good.tar);
    tampered[600] ^= 0xff;
    await expect(fetchReferences([submission!], tmpDir(), { fetch: registry(new Map([[good.digest, tampered]])) }))
      .rejects.toThrow("does not match its recorded digest");
    // a member outside the layer's allowlist, a directory entry, a prefix-field escape
    for (const mutate of [
      (entries: TarEntry[]) => { entries[0]!.name = "./proofs/lib/Lax38Proofs/Basic.ilean"; },
      (entries: TarEntry[]) => { entries.unshift({ name: "./concepts/", type: "5" }); },
      (entries: TarEntry[]) => { entries[1]!.name = "../Order.lean"; },
      (entries: TarEntry[]) => { entries[1]!.name = "./concepts/package/Lax38/Order.lean"; entries[1]!.prefix = "./concepts/package"; },
      (entries: TarEntry[]) => { entries[1]!.corruptChecksum = true; },
    ]) {
      const bad = layer(concept.sourceText, mutate);
      declare(bad);
      await expect(fetchReferences([submission!], tmpDir(), { fetch: registry(new Map([[bad.digest, bad.tar]])) }))
        .rejects.toThrow(/disallowed name|not a regular file|ustar header/u);
    }
    // the displayed source must be byte-equal to the sealed one
    const drifted = layer(`${concept.sourceText}-- drift\n`);
    declare(drifted);
    await expect(fetchReferences([submission!], tmpDir(), { fetch: registry(new Map([[drifted.digest, drifted.tar]])) }))
      .rejects.toThrow("does not match displayed source");
    // a layer that is not a whole number of tar records is refused before any fetch
    submission!.output!.capture!.references = { digest: good.digest, bytes: good.tar.length - 512, registryBlob: blob(good.digest) };
    await expect(fetchReferences([submission!], tmpDir(), { fetch: () => { throw new Error("unexpected network"); } }))
      .rejects.toThrow("unsupported or invalid references layer");
  });

  it("has nothing to fetch for a spec-2 record whose layer address was withheld", async () => {
    const [, submission] = loadSubmissions(database());
    delete submission!.output!.capture!.references!.registryBlob;
    expect(await fetchReferences([submission!], tmpDir(), { fetch: () => { throw new Error("unexpected network"); } })).toEqual([]);
    expect(loadReferences(submission!, tmpDir())).toBeUndefined();
  });
});

describe("spec-2 records on the site", () => {
  async function site(): Promise<{ root: string; read: (file: string) => string }> {
    const root = tmpDir("lax-spec2-site-");
    await generateSite(loadSubmissions(database()), root);
    return { root, read: (file) => fs.readFileSync(path.join(root, file), "utf8") };
  }

  it("shows the telescope on proof cards, in binder order with the Challenge's names", async () => {
    const { read } = await site();
    const proof = read("lax-38/Lax38Proofs.refl_of_hasSucc.html");
    const card = proof.slice(proof.indexOf('<ol class="judgment-telescope">'), proof.indexOf("</ol>"));
    expect(card).toContain('<li><span class="telescope-name">h₁</span>');
    expect(card).toContain('<li><span class="telescope-name">h₂</span>');
    // binder kinds are not recorded, so the card labels none
    expect(card).not.toContain("binder");
    // both hypotheses link to the exact statement, not the concept
    expect(card.match(/href="\.\.\/lax-38\/Lax38\.Order\.html#s-Lax38\.Order\.HasSucc"/gu)).toHaveLength(2);
    expect(proof).toContain("Assuming the hypotheses on the left, in binder order");
    expect(proof).toContain("composed by this site from the archive's edges");
    // a proof without hypotheses says so
    expect(read("lax-38/Lax38Proofs.hasSucc.html")).toContain('<p class="judgment-unconditional">no hypotheses</p>');
    // the derived status is still composed, and still shown as before
    expect(proof).toContain('class="status-pill pill-proven"');
  });

  it("marks a certified record and its proofs, with the rerun command", async () => {
    const { read } = await site();
    const mark = "certified: lake comparator (Lean v4.35.0, kernels lean)";
    const proof = read("lax-38/Lax38Proofs.refl_of_hasSucc.html");
    expect(proof).toContain(`<span class="certified-mark-text">${mark}</span>, bundle <code>${"3".repeat(64)}</code>`);
    expect(proof).toContain("<code>lax certify lax-38 --run</code>");
    expect(proof).toContain("<code>lake comparator --config comparator.json</code>");
    const record = read("lax-38/index.html");
    expect(record).toContain(`<span class="certified-mark-text">${mark}</span>`);
    expect(record.match(/class="certified-mark certified-mark-compact" title="certified: lake comparator/gu)).toHaveLength(2);
    // under the proof network, before the proof list
    expect(record.indexOf('id="proof-network"')).toBeLessThan(record.indexOf('class="certificate-block"'));
    expect(record.indexOf('class="certificate-block"')).toBeLessThan(record.indexOf("<summary>Proof list</summary>"));
  });

  it("shows the Challenge verbatim, collapsed, beside the bundle and export digests", async () => {
    const { read } = await site();
    const record = read("lax-38/index.html");
    const challenge = storedRecord().certificate.challenge as string;
    expect(record).toContain('<details class="figure-details challenge-details">\n<summary>Challenge</summary>');
    expect(record).not.toContain('<details class="figure-details challenge-details" open>');
    expect(record).toContain(`<pre class="challenge-source"><code>${challenge.replace(/</gu, "&lt;")}</code></pre>`);
    expect(record).toContain(`bundle <code>${"3".repeat(64)}</code><br>challenge export <code>${"4".repeat(64)}</code><br>proof package export <code>${"7".repeat(64)}</code></p>`);
  });

  it("states the trust model once per spec-2 record page, with its environment", async () => {
    const { read } = await site();
    const record = read("lax-38/index.html");
    expect(record.match(/class="trust-note"/gu)).toHaveLength(1);
    expect(record).toContain("In environment <code>v4.35.0</code> (spec 2) the edges of a proof network are certified by Lean's <code>lake comparator</code>");
    expect(record).toContain("the concept packages a record depends on are trusted for their meaning, as in every environment");
    // what a rerun needs, not a promise the bundle alone keeps (ultracode M1)
    expect(record).toContain("a certificate can be rerun with <code>lax certify --run</code> from the archive's own captures of the packages, which additionally trusts that those captures hold the sources of the commits the records name, or by hand from its bundle while the authors' repositories still serve them");
    expect(record).not.toContain("every certificate can be rerun from its bundle");
  });

  it("shows no mark on a spec-2 record without proofs, and nothing new on a spec-1 record", async () => {
    const root = database((dir) => {
      fs.mkdirSync(path.join(dir, "lax-39"));
      fs.writeFileSync(path.join(dir, "lax-39", "record.json"), JSON.stringify({ specVersion: "1", id: "lax-39", state: "draft", createdAt: "2026-10-03T00:00:00Z" }));
      const stored = storedRecord();
      stored.proofs = [];
      delete stored.certificate;
      stored.inputs.manifest.title = "Definitions only";
      stored.inputs.abstract = "No proofs, so nothing was judged.";
      stored.concepts = [{
        id: "Lax39.Defs", path: "concepts/Lax39/Defs.lean", title: "A definition", type: "definition", description: "Just a def.",
        imports: [], mathlibImports: [], sourceText: "namespace Lax39.Defs\ndef two : Nat := 2\nend Lax39.Defs\n", statements: [],
      }];
      fs.writeFileSync(path.join(dir, "lax-39", "build-output.json"), JSON.stringify(stored));
    });
    const out = tmpDir("lax-spec2-nomark-");
    await generateSite(loadSubmissions(root), out);
    const read = (file: string) => fs.readFileSync(path.join(out, file), "utf8");
    const noProofs = read("lax-39/index.html");
    expect(noProofs).toContain("No proofs in this submission.");
    for (const marker of ["certified", "certificate-block", "trust-note", "challenge-details"]) expect(noProofs).not.toContain(marker);
    for (const file of ["lax-2/index.html", "lax-2/Lax2Proofs.truth.html", "lax-2/Lax2.C.html"]) {
      const html = read(file);
      for (const marker of ["certified", "certificate-block", "trust-note", "judgment-telescope", "telescope-name", "challenge"]) expect(html).not.toContain(marker);
    }
    expect(read("lax-2/Lax2Proofs.truth.html")).toContain("checked by the archive's pipeline");
    // the certified mark keys on proofs and the certificate together
    const output = loadSubmissions(root).find((s) => s.record.id === "lax-39")!.output!;
    expect(isCertified(output)).toBe(false);
  });

  it("shows a pending edge's type marked pending, never certified, and proves nothing with it", async () => {
    // lax-42: a draft whose one proof is a pending edge concluding lax-38's
    // Refl from nothing, so it has no certificate; lax-38 stays complete.
    const root = database((dir) => {
      fs.mkdirSync(path.join(dir, "lax-42"));
      fs.writeFileSync(path.join(dir, "lax-42", "record.json"), JSON.stringify({ specVersion: "1", id: "lax-42", state: "draft", createdAt: "2026-10-05T00:00:00Z" }));
      const stored = storedRecord();
      stored.id = "lax-42";
      stored.inputs.manifest.title = "Stub first";
      stored.concepts = [];
      stored.proofs = [{ ...stored.proofs[1], id: "Lax42Proofs.refl", path: "proofs/Lax42Proofs/Basic.lean", pending: true,
        telescope: { hypotheses: [], conclusion: stored.proofs[1].telescope.conclusion } }];
      delete stored.certificate;
      fs.writeFileSync(path.join(dir, "lax-42", "build-output.json"), JSON.stringify(stored));
    });
    const submissions = loadSubmissions(root);
    const model = new SiteModel(submissions);
    expect(model.network.proven.has("Lax38.Order.Refl")).toBe(true); // through lax-38's own complete edge
    const out = tmpDir("lax-spec2-pending-");
    await generateSite(submissions, out);
    const read = (file: string) => fs.readFileSync(path.join(out, file), "utf8");
    const proof = read("lax-42/Lax42Proofs.refl.html");
    expect(proof).toContain('<div class="judgment judgment-spec2">');
    expect(proof).toContain('class="status-pill pill-none"');
    expect(proof).toContain(">pending (proof contains sorry)</span>");
    expect(proof).toContain("its Lean proof contains <code>sorry</code>. It is not in the record's Challenge, is not certified");
    for (const marker of ["certified-mark", "lax certify", "pill-proven", "grounded"]) expect(proof).not.toContain(marker);
    const record = read("lax-42/index.html");
    expect(record).toContain('<span class="pending-mark" title=');
    expect(record).toContain('<p class="pending-note">One edge is pending (proof contains sorry)');
    for (const marker of ["certified-mark", "challenge-details", "trust-note"]) expect(record).not.toContain(marker);
    const data = JSON.parse(/<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/u.exec(record)![1]!);
    expect(data.proofs.proofs).toContainEqual(expect.objectContaining({ id: "Lax42Proofs.refl", owner: "lax-42", pending: true }));
    expect(data.proofs.proofs.filter((entry: { pending?: boolean }) => entry.pending)).toHaveLength(1);
    expect(data.proofs.details["proof:Lax42Proofs.refl"]).toMatchObject({ status: "pending", statusDetail: "pending (proof contains sorry)" });
    expect(record).toContain('class="legend-proof-chip legend-pending"');
    // a pending edge never fires in the network
    const alone = storedRecord();
    alone.proofs[0].pending = true;
    alone.proofs[1].pending = true;
    delete alone.certificate;
    const output = rendererOutput(alone, "x", "lax-38")!;
    const pendingModel = new SiteModel([{ record: submissions.find((s) => s.record.id === "lax-38")!.record, output }]);
    expect(pendingModel.network.proven.size).toBe(0);
    expect(isCertified(output)).toBe(false);
  });

  it("marks a complete proof certified and a pending one beside it pending", async () => {
    const root = database((dir) => {
      const stored = storedRecord();
      stored.proofs[1].pending = true;
      fs.writeFileSync(path.join(dir, "lax-38", "build-output.json"), JSON.stringify(stored));
    });
    const out = tmpDir("lax-spec2-mixed-");
    await generateSite(loadSubmissions(root), out);
    const read = (file: string) => fs.readFileSync(path.join(out, file), "utf8");
    const record = read("lax-38/index.html");
    expect(record.match(/class="certified-mark certified-mark-compact"/gu)).toHaveLength(1);
    expect(record.match(/class="pending-mark"/gu)).toHaveLength(1);
    expect(record).toContain("Every complete proof of this record, stated over its concept packages alone");
    expect(record.indexOf('class="pending-note"')).toBeLessThan(record.indexOf("<summary>Challenge</summary>"));
    expect(read("lax-38/Lax38Proofs.refl_of_hasSucc.html")).not.toContain("certified-mark");
    expect(read("lax-38/Lax38Proofs.hasSucc.html")).toContain("certified-mark-line");
  });

  it("keeps the raw statement body off the page: the source is the shown form", async () => {
    const { read } = await site();
    const concept = read("lax-38/Lax38.Order.html");
    expect(concept).not.toContain("Exists fun");
    expect(concept).toContain('id="s-Lax38.Order.HasSucc"');
    const text = concept.replace(/<[^>]+>/gu, "").replace(/&lt;/gu, "<").replace(/&gt;/gu, ">").replace(/&amp;/gu, "&");
    expect(text).toContain("@[lax_statement] def HasSucc : Prop := ∀ n : Nat, ∃ m, n < m");
  });

  it("writes each environment's spec version to environments.json", async () => {
    const { read } = await site();
    expect(JSON.parse(read("environments.json"))).toEqual({
      epoch: "v4.33.0",
      environments: [
        { id: "v4.33.0", specVersion: 1, registered: 1, drafts: 0 },
        { id: "v4.35.0", specVersion: 2, registered: 1, drafts: 0 },
      ],
    });
    // an environment with records takes its spec from them; an empty one
    // from the caller, then the site's table, then the v4.35 rule
    const submissions = loadSubmissions(database());
    expect(environmentIndex(new SiteModel(submissions, "v4.36.0", { "v4.36.0": 1 })).environments[0])
      .toEqual({ id: "v4.36.0", specVersion: 1, registered: 0, drafts: 0 });
    expect(environmentIndex(new SiteModel(submissions, "v4.36.0")).environments[0])
      .toEqual({ id: "v4.36.0", specVersion: 2, registered: 0, drafts: 0 });
    expect(ENVIRONMENT_SPEC_VERSIONS["v4.35.0"]).toBe(2);
    expect(environmentSpecVersion("v4.34.0")).toBe(1);
    expect(environmentSpecVersion("v5.0.0")).toBe(2);
    expect(environmentSpecVersion("v4.35.1")).toBe(2);
  });

  it("skips a record whose spec disagrees with its environment's other records", async () => {
    const root = database((dir) => {
      fs.mkdirSync(path.join(dir, "lax-41"));
      fs.writeFileSync(path.join(dir, "lax-41", "record.json"), JSON.stringify({ specVersion: "1", id: "lax-41", state: "draft", createdAt: "2026-10-03T00:00:00Z" }));
      fs.writeFileSync(path.join(dir, "lax-41", "build-output.json"), JSON.stringify({
        specVersion: "1", id: "lax-41",
        inputs: { manifest: { specVersion: "1", id: "lax-41", leanVersion: "v4.35.0", mathlibVersion: "e".repeat(40), title: "Odd one", authors: [], bibEntries: [] }, abstract: "" },
        requiredByConcepts: [], requiredByProofs: [], concepts: [], proofs: [],
      }));
    });
    const out = tmpDir("lax-spec2-conflict-");
    const skipped: Array<{ id: string; reason: string }> = [];
    await generateSite(loadSubmissions(root), out, { onSkip: (skip) => skipped.push(skip) });
    expect(skipped).toEqual([{ id: "lax-41", reason: "record follows spec 1 in environment v4.35.0, whose records follow spec 2" }]);
    expect(fs.existsSync(path.join(out, "lax-38", "index.html"))).toBe(true);
    expect(fs.existsSync(path.join(out, "lax-41"))).toBe(false);
  });

  it("renders a spec-2 record handed over already expanded, as lax serve does", async () => {
    // lax's own loader expands the record (recorded-shape.ts) and withholds
    // the capture address; the renderer must need neither the stored shape
    // nor the layer to draw the page.
    const output = rendererOutput(storedRecord(), "x", "lax-38") as BuildOutput;
    delete output.capture!.registryBlob;
    const submission: SiteSubmission = {
      record: JSON.parse(fs.readFileSync(path.join(FIXTURE, "lax-38", "record.json"), "utf8")),
      output,
    };
    const out = tmpDir("lax-spec2-expanded-");
    await generateSite([submission], out, "v4.35.0");
    const record = fs.readFileSync(path.join(out, "lax-38", "index.html"), "utf8");
    expect(record).toContain('class="certificate-block"');
    expect(record).toContain('<span class="meta-epoch"');
  });
});

describe("pages named by an id with a `?`", () => {
  // The archive's name grammar admits `?` (`get?`, ultracode review C3); a
  // raw `get?.html` href would request `get` with the query `.html`.
  it("writes the file under the raw id and links it percent-encoded", async () => {
    const root = database((dir) => {
      fs.mkdirSync(path.join(dir, "lax-3"));
      fs.writeFileSync(path.join(dir, "lax-3", "record.json"), JSON.stringify({
        specVersion: "1", id: "lax-3", state: "registered", createdAt: "2026-01-01T00:00:00Z", registeredAt: "2026-01-02T00:00:00Z",
      }));
      fs.writeFileSync(path.join(dir, "lax-3", "build-output.json"), JSON.stringify({
        specVersion: "1", id: "lax-3",
        inputs: {
          manifest: { specVersion: "1", id: "lax-3", leanVersion: "v4.33.0", mathlibVersion: "c".repeat(40), title: "Three", authors: [], bibEntries: [] },
          abstract: "Names with a question mark.",
        },
        requiredByConcepts: [], requiredByProofs: [],
        concepts: [{
          id: "Lax3.ok?", path: "concepts/Lax3/C.lean", title: "Truth", type: "theorem", description: "d", imports: [], mathlibImports: [],
          sourceText: "namespace Lax3\naxiom ok? : True\nend Lax3\n",
          statements: [{ id: "Lax3.ok?.holds?", signature: "holds? : True", startLine: 2, endLine: 2 }],
        }],
        proofs: [{ id: "Lax3Proofs.get?", path: "proofs/Lax3Proofs/Basic.lean", conclusion: "Lax3.ok?.holds?", assumptions: [], description: "Direct." }],
      }));
    });
    const out = tmpDir("lax-question-site-");
    await generateSite(loadSubmissions(root), out);
    const read = (file: string) => fs.readFileSync(path.join(out, file), "utf8");
    expect(fs.existsSync(path.join(out, "lax-3", "Lax3Proofs.get?.html"))).toBe(true);
    expect(fs.existsSync(path.join(out, "lax-3", "Lax3.ok?.html"))).toBe(true);
    const index = read("lax-3/index.html");
    expect(index).toContain('href="../lax-3/Lax3Proofs.get%3F.html"');
    expect(index).toContain("Lax3.ok%3F.html");
    // no link anywhere on the record's pages leaves the `?` raw
    for (const file of ["lax-3/index.html", "lax-3/Lax3Proofs.get?.html", "lax-3/Lax3.ok?.html"])
      expect(read(file)).not.toMatch(/href="[^"]*\?\.html/u);
    expect(read("sitemap.xml")).toContain("/lax-3/Lax3Proofs.get%3F.html</loc>");
    expect(read("lax-3/Lax3Proofs.get?.html")).toContain('rel="canonical" href="https://');
    expect(read("lax-3/Lax3Proofs.get?.html")).toMatch(/rel="canonical" href="[^"]*Lax3Proofs\.get%3F\.html"/u);
  });
});
