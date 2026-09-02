// The papers cache: one `<digest>.pdf` per compiled paper the database
// references, filled from the archive's capture registry before a build so
// the generator stays a pure function of files on disk and never fetches.
//
// The archive pushes each PDF as a digest-addressed blob of the submission's
// capture (`registryBlob` in the record's `paper.pdf`), which ghcr hands out
// anonymously. The transport rules mirror the CLI's dependency download:
// an anonymous pull token, bounded redirects to the known public hosts,
// a size cap, and the bytes verified against the digest before they land.

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import type { SiteSubmission } from "./sitegen/model.js";

const REGISTRY_HOST = "ghcr.io";
const REDIRECT_HOSTS = new Set([REGISTRY_HOST, "pkg-containers.githubusercontent.com"]);
const MAX_REDIRECTS = 5;
/** The archive's own cap on a compiled paper; anything larger is not ours.
 * The derived web bundles share the cap (`capture-store` precedent). */
export const MAX_PAPER_BYTES = 25 * 1024 * 1024;
/** A ghcr digest address as the archive records it (`registryBlob`). */
export const BLOB_REFERENCE =
  /^ghcr\.io\/([a-z0-9]+(?:[._-][a-z0-9]+)*(?:\/[a-z0-9]+(?:[._-][a-z0-9]+)*)+)@sha256:([0-9a-f]{64})$/u;

export function paperCachePath(papersDir: string, digest: string): string {
  if (!/^[0-9a-f]{64}$/u.test(digest)) throw new Error(`paper digest is not sha256 hex: ${digest}`);
  return path.join(path.resolve(papersDir), `${digest}.pdf`);
}

export interface PaperReference {
  submissionId: string;
  digest: string;
  registryBlob: string;
}

/** Every distinct paper the listed submissions reference, by digest. */
export function paperReferences(submissions: SiteSubmission[]): PaperReference[] {
  const byDigest = new Map<string, PaperReference>();
  for (const submission of submissions) {
    if (submission.record.state === "deleted") continue;
    const paper = submission.output?.paper;
    if (!paper) continue;
    if (paper.pdf.registryBlob === undefined)
      throw new Error(`${submission.record.id} declares a paper without a registry blob`);
    const match = BLOB_REFERENCE.exec(paper.pdf.registryBlob);
    if (match === null || match[2] !== paper.pdf.digest)
      throw new Error(`${submission.record.id} paper registryBlob is not a ghcr address of its digest`);
    if (!byDigest.has(paper.pdf.digest))
      byDigest.set(paper.pdf.digest, { submissionId: submission.record.id, digest: paper.pdf.digest, registryBlob: paper.pdf.registryBlob });
  }
  return [...byDigest.values()].sort((a, b) => a.digest.localeCompare(b.digest));
}

export interface FetchOptions {
  fetch?: typeof fetch;
  log?: (line: string) => void;
}

/** Download every referenced paper the cache lacks. Returns the digests fetched. */
export async function fetchPapers(
  submissions: SiteSubmission[],
  papersDir: string,
  options: FetchOptions = {},
): Promise<string[]> {
  const doFetch = options.fetch ?? fetch;
  const log = options.log ?? (() => {});
  fs.mkdirSync(path.resolve(papersDir), { recursive: true });
  const fetched: string[] = [];
  for (const reference of paperReferences(submissions)) {
    const file = paperCachePath(papersDir, reference.digest);
    if (fs.existsSync(file)) continue;
    log(`fetching paper of ${reference.submissionId} (${reference.digest.slice(0, 12)})`);
    const bytes = await downloadBlob(reference.registryBlob, doFetch);
    const digest = createHash("sha256").update(bytes).digest("hex");
    if (digest !== reference.digest)
      throw new Error(`paper of ${reference.submissionId} downloaded with digest ${digest}, expected ${reference.digest}`);
    if (bytes.subarray(0, 5).toString("latin1") !== "%PDF-")
      throw new Error(`paper of ${reference.submissionId} is not a PDF`);
    const temporary = `${file}.${process.pid}.part`;
    fs.writeFileSync(temporary, bytes, { mode: 0o644 });
    fs.renameSync(temporary, file);
    fetched.push(reference.digest);
  }
  return fetched;
}

/** Download one public registry blob by its recorded address — anonymous
 * pull token, bounded redirects to the known hosts, size-capped. Shared by
 * the papers and bundles caches; callers verify the digest of what arrives. */
export async function downloadBlob(reference: string, doFetch: typeof fetch): Promise<Buffer> {
  const match = BLOB_REFERENCE.exec(reference);
  if (match === null) throw new Error(`not a ghcr digest reference: ${reference}`);
  const [, repository, digest] = match;
  // Public packages hand out pull tokens anonymously; no credential is sent.
  const tokenResponse = await doFetch(
    `https://${REGISTRY_HOST}/token?service=${REGISTRY_HOST}&scope=${encodeURIComponent(`repository:${repository}:pull`)}`,
    { signal: AbortSignal.timeout(60_000) },
  );
  if (tokenResponse.status !== 200) throw new Error(`ghcr token request failed with HTTP ${tokenResponse.status}`);
  const token = (JSON.parse(await tokenResponse.text()) as { token?: unknown }).token;
  if (typeof token !== "string" || token === "" || /[\s"\\]/u.test(token))
    throw new Error("ghcr token response is malformed");

  let url = new URL(`https://${REGISTRY_HOST}/v2/${repository}/blobs/sha256:${digest}`);
  let response: Response | undefined;
  for (let redirects = 0; redirects <= MAX_REDIRECTS; redirects += 1) {
    // The bearer token goes only to the registry itself; redirect targets are
    // pre-signed URLs that must never see it.
    const headers: Record<string, string> = url.hostname === REGISTRY_HOST ? { authorization: `Bearer ${token}` } : {};
    response = await doFetch(url, { headers, redirect: "manual", signal: AbortSignal.timeout(10 * 60_000) });
    if (![301, 302, 303, 307, 308].includes(response.status)) break;
    const location = response.headers.get("location");
    if (location === null || redirects === MAX_REDIRECTS) throw new Error("paper download has an invalid redirect chain");
    url = new URL(location, url);
    if (url.protocol !== "https:" || !REDIRECT_HOSTS.has(url.hostname) || url.username || url.password)
      throw new Error("paper redirect leaves the allowed public HTTPS locations");
  }
  if (response === undefined || !response.ok) throw new Error(`paper download failed with HTTP ${response?.status ?? "?"}`);
  const length = Number(response.headers.get("content-length") ?? "0");
  if (length > MAX_PAPER_BYTES) throw new Error(`paper exceeds ${MAX_PAPER_BYTES} bytes`);
  const bytes = Buffer.from(await response.arrayBuffer());
  if (bytes.length > MAX_PAPER_BYTES) throw new Error(`paper exceeds ${MAX_PAPER_BYTES} bytes`);
  return bytes;
}
