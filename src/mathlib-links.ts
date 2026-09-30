import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { gunzipSync } from "node:zlib";
import type { SiteSubmission } from "./sitegen/model.js";
import type { FetchOptions } from "./papers.js";

const DOCS = "https://leanprover-community.github.io/mathlib4_docs/";
const MODULE = /^Mathlib(?:\.[A-Za-z0-9_]+)+$/u;
const COMMIT = /^[0-9a-f]{40}$/u;
const sha256 = (bytes: Buffer) => createHash("sha256").update(bytes).digest("hex");
let declarations: Record<string, unknown> | undefined;

/** Only the vendored index is consulted during rendering. No network or
 * mutable latest-version lookup can change the output of a build. */
function docsIndex(): Record<string, unknown> {
  if (declarations) return declarations;
  const directory = new URL("../assets/mathlib-docs/", import.meta.url);
  const snapshot = JSON.parse(fs.readFileSync(new URL("snapshot.json", directory), "utf8"));
  const bytes = fs.readFileSync(new URL("declarations.json.gz", directory));
  if (sha256(bytes) !== snapshot.sha256) throw new Error("Mathlib documentation snapshot checksum mismatch");
  const value = JSON.parse(gunzipSync(bytes, { maxOutputLength: 80 * 1024 * 1024 }).toString("utf8"));
  if (!value || typeof value !== "object" || Array.isArray(value) || Object.keys(value).length !== snapshot.declarations)
    throw new Error("invalid Mathlib documentation snapshot");
  return declarations = value;
}

/** Also used at the final HTML boundary. An arbitrary external URL is never
 * accepted just because a caller supplies it as a source decoration. */
export function mathlibLinkTitle(href: string): string | undefined {
  if (!href.startsWith("https://")) return undefined;
  let url: URL;
  try { url = new URL(href); } catch { return undefined; }
  if (url.protocol !== "https:" || url.username || url.password || url.port || url.search) return undefined;
  if (url.origin === "https://leanprover-community.github.io" &&
    /^\/mathlib4_docs\/Mathlib\/(?:[A-Za-z0-9_]+\/)*[A-Za-z0-9_]+\.html$/u.test(url.pathname) && url.hash)
    return "Mathlib documentation (current version; may differ from this submission)";
  if (url.origin === "https://github.com" && !url.hash &&
    /^\/leanprover-community\/mathlib4\/blob\/[0-9a-f]{40}\/Mathlib\/(?:[A-Za-z0-9_]+\/)*[A-Za-z0-9_]+\.lean$/u.test(url.pathname))
    return "Mathlib source at this submission’s pinned version (defining module)";
  return undefined;
}

export function mathlibDocLink(module: string, name: string): string | undefined {
  if (!MODULE.test(module)) return undefined;
  const index = docsIndex();
  const link = Object.hasOwn(index, name) ? index[name] : undefined;
  if (typeof link !== "string" || !link.startsWith("./Mathlib/")) return undefined;
  const href = new URL(link, DOCS).href;
  return mathlibLinkTitle(href) ? href : undefined;
}

function sourceTarget(submission: SiteSubmission, module: string): { href: string; key: string } | undefined {
  const commit = submission.output?.capture?.mathlibCommit ?? submission.output?.manifest.mathlibVersion;
  if (!commit || !COMMIT.test(commit) || !MODULE.test(module)) return undefined;
  const key = `${commit}/${module.replaceAll(".", "/")}.lean`;
  return { key, href: `https://github.com/leanprover-community/mathlib4/blob/${key}` };
}

function missingModules(submission: SiteSubmission): string[] {
  const missing = new Set<string>();
  for (const references of submission.sourceReferences?.values() ?? [])
    for (const ref of references.constants)
      if (ref.usages.length && MODULE.test(ref.module) && !mathlibDocLink(ref.module, ref.name)) missing.add(ref.module);
  return [...missing].sort();
}

function cacheFile(directory: string, key: string): string {
  return path.join(directory, "mathlib-sources", `${key}.json`);
}

function cachedSource(directory: string, key: string): boolean | undefined {
  const file = cacheFile(directory, key);
  if (!fs.existsSync(file)) return undefined;
  const data = JSON.parse(fs.readFileSync(file, "utf8"));
  if (data.key !== key || typeof data.exists !== "boolean") throw new Error(`invalid Mathlib source cache: ${key}`);
  return data.exists;
}

/** Only modules positively checked at the immutable source URL get fallback
 * links. A 404 is cached too; outages never become permanent negative results. */
export async function fetchMathlibSources(submissions: SiteSubmission[], directory: string, options: FetchOptions = {}): Promise<void> {
  for (const submission of submissions) for (const module of missingModules(submission)) {
    const target = sourceTarget(submission, module);
    if (!target || cachedSource(directory, target.key) !== undefined) continue;
    options.log?.(`checking pinned Mathlib source ${target.key}`);
    const response = await (options.fetch ?? fetch)(`https://raw.githubusercontent.com/leanprover-community/mathlib4/${target.key}`,
      { method: "HEAD", redirect: "error", signal: AbortSignal.timeout(30_000) });
    if (response.status !== 200 && response.status !== 404)
      throw new Error(`Mathlib source check failed with HTTP ${response.status}: ${target.key}`);
    const file = cacheFile(directory, target.key);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    const temporary = `${file}.${process.pid}.tmp`;
    fs.writeFileSync(temporary, JSON.stringify({ key: target.key, exists: response.status === 200 }) + "\n");
    fs.renameSync(temporary, file);
  }
}

export function loadMathlibSources(submission: SiteSubmission, directory: string): Map<string, string> {
  const links = new Map<string, string>();
  for (const module of missingModules(submission)) {
    const target = sourceTarget(submission, module);
    if (!target) continue;
    const exists = cachedSource(directory, target.key);
    if (exists === undefined) throw new Error(`Mathlib source cache is missing ${target.key}; run \`npm run references:fetch\``);
    if (exists) links.set(module, target.href);
  }
  return links;
}
