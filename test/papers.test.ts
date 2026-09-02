import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { fetchPapers, MAX_PAPER_BYTES, paperCachePath, paperReferences } from "../src/papers.js";
import type { SiteSubmission } from "../src/sitegen/model.js";
import { tmpDir } from "./helpers.js";

const pdf = Buffer.from("%PDF-1.7\n%fixture\n");
const digest = createHash("sha256").update(pdf).digest("hex");

function submission(id: string, paper: boolean, state = "registered"): SiteSubmission {
  return {
    record: { specVersion: "1", id, state: state as "registered", createdAt: "2026-09-01T00:00:00Z" },
    output: {
      specVersion: "1", id,
      manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: id, authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [], concepts: [], proofs: [],
      ...(paper ? { paper: {
        folder: "paper", main: "main.tex", engine: "pdflatex",
        pdf: { digest, bytes: pdf.length, pages: 1, registryBlob: `ghcr.io/lax-archive/lax-captures@sha256:${digest}` },
        pageSizes: [[595.28, 841.89]], marks: [],
      } } : {}),
    },
  };
}

/** ghcr as the CLI's download tool observed it: an anonymous token, then a
 * 307 from the blob endpoint to a pre-signed URL that must not see the token. */
function fakeRegistry(body: Buffer, log: { url: string; auth: string | null }[]): typeof fetch {
  return async (input, init) => {
    const url = String(input);
    const headers = new Headers(init?.headers);
    log.push({ url, auth: headers.get("authorization") });
    if (url.startsWith("https://ghcr.io/token?"))
      return new Response(JSON.stringify({ token: "anon-token" }), { status: 200 });
    if (url.startsWith("https://ghcr.io/v2/lax-archive/lax-captures/blobs/sha256:"))
      return new Response(null, { status: 307, headers: { location: "https://pkg-containers.githubusercontent.com/ghcr1/blobs/x?se=1" } });
    if (url.startsWith("https://pkg-containers.githubusercontent.com/"))
      return new Response(body, { status: 200, headers: { "content-length": String(body.length) } });
    return new Response("nope", { status: 404 });
  };
}

describe("papers cache", () => {
  it("names cache files by digest and lists each referenced paper once", () => {
    expect(paperCachePath("/cache", digest)).toBe(path.join("/cache", `${digest}.pdf`));
    expect(() => paperCachePath("/cache", "../etc/passwd")).toThrow("not sha256 hex");
    const references = paperReferences([submission("lax-1", false), submission("lax-2", true), submission("lax-3", true), submission("lax-4", true, "deleted")]);
    expect(references).toEqual([{ submissionId: "lax-2", digest, registryBlob: `ghcr.io/lax-archive/lax-captures@sha256:${digest}` }]);
    const bad = submission("lax-9", true);
    bad.output!.paper!.pdf.registryBlob = `ghcr.io/lax-archive/lax-captures@sha256:${"0".repeat(64)}`;
    expect(() => paperReferences([bad])).toThrow("not a ghcr address of its digest");
  });

  it("downloads missing papers anonymously, verifies the digest, and skips cached ones", async () => {
    const cache = tmpDir("lax-papers-");
    const log: { url: string; auth: string | null }[] = [];
    const submissions = [submission("lax-2", true)];
    expect(await fetchPapers(submissions, cache, { fetch: fakeRegistry(pdf, log) })).toEqual([digest]);
    expect(fs.readFileSync(paperCachePath(cache, digest))).toEqual(pdf);
    expect(log.map((entry) => entry.auth)).toEqual([null, "Bearer anon-token", null]);
    expect(fs.readdirSync(cache)).toEqual([`${digest}.pdf`]);
    log.length = 0;
    expect(await fetchPapers(submissions, cache, { fetch: fakeRegistry(pdf, log) })).toEqual([]);
    expect(log).toEqual([]);
  });

  it("rejects bytes that do not hash to the recorded digest, non-PDFs, and oversize blobs", async () => {
    const submissions = [submission("lax-2", true)];
    await expect(fetchPapers(submissions, tmpDir("lax-papers-bad-"), { fetch: fakeRegistry(Buffer.from("%PDF-1.7 other"), []) }))
      .rejects.toThrow("downloaded with digest");
    const notPdf = Buffer.from("plain text");
    const other = submission("lax-2", true);
    other.output!.paper!.pdf.digest = createHash("sha256").update(notPdf).digest("hex");
    other.output!.paper!.pdf.registryBlob = `ghcr.io/lax-archive/lax-captures@sha256:${other.output!.paper!.pdf.digest}`;
    await expect(fetchPapers([other], tmpDir("lax-papers-bad-"), { fetch: fakeRegistry(notPdf, []) })).rejects.toThrow("is not a PDF");
    const huge: typeof fetch = async (input) => {
      const url = String(input);
      if (url.includes("/token?")) return new Response(JSON.stringify({ token: "t" }), { status: 200 });
      return new Response("", { status: 200, headers: { "content-length": String(MAX_PAPER_BYTES + 1) } });
    };
    await expect(fetchPapers(submissions, tmpDir("lax-papers-bad-"), { fetch: huge })).rejects.toThrow("exceeds");
    const escape: typeof fetch = async (input) => {
      const url = String(input);
      if (url.includes("/token?")) return new Response(JSON.stringify({ token: "t" }), { status: 200 });
      return new Response(null, { status: 307, headers: { location: "https://evil.example/blob" } });
    };
    await expect(fetchPapers(submissions, tmpDir("lax-papers-bad-"), { fetch: escape })).rejects.toThrow("leaves the allowed");
  });
});
