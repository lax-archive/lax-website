// From a cached reflow bundle to what the paper page embeds and the site
// emits: the schema gate first (the deploy-safety rule — the build renders
// every page with the *current* vendored viewer over old bundles, so a
// bundle whose recorded schema the viewer does not support drops that page
// to the PDF-only surface with a log line, never a broken reflow page),
// then the fonts pipeline (every served font name content-hashed and
// emitted under the site root's `fonts/`, referenced through the per-page
// font-map island), then the embed budget (blocks ride inline as base64 up
// to the budget; past it they ship as same-origin files the viewer fetches
// — `connect-src 'self'` already allows that, no CSP change).

import { createHash } from "node:crypto";
import fs from "node:fs";
import { readPaperBundle } from "../bundles.js";
import { siteAssetPath } from "./assets.js";
import type { SiteSubmission } from "./model.js";

/** Base64 inflates 4/3, so a 25 MiB bundle would be a ~33 MB page; blocks
 * embed inline only while the page stays comfortably readable. */
export const EMBED_BUDGET_BYTES = 2 * 1024 * 1024;

/** The bundle format this build knows how to lay onto a page. */
const SUPPORTED_FORMAT_VERSION = 1;
const SUPPORTED_TOOL = "reflowtex";

/** What the paper page needs from a gated, extracted bundle. */
export interface PaperWebPage {
  /** `schema/latex.proto`, base64, for the viewer's schema island. */
  schemaB64: string;
  /** Original font name (as blocks reference it) → hashed served name
   * under the site root's `fonts/`, for the font-map island. */
  fontMap: Record<string, string>;
  /** One entry per block, in document order: embedded bytes or the
   * page-relative file the viewer fetches. */
  blocks: Array<{ b64: string } | { src: string }>;
}

export interface PreparedPaperWeb {
  page: PaperWebPage;
  /** Site-relative output files this page adds: hashed fonts at the root
   * `fonts/`, and `<id>/paper-web/*.pb` when past the embed budget. */
  files: Array<[string, Buffer]>;
}

/**
 * The vendored viewer's supported schema set. It lives beside the viewer it
 * describes (`assets/site/reflowtex/supported-schemas.json`) and must be
 * extended in the same change that revendors a viewer understanding a new
 * schema — the fixture regeneration rule in `test/fixtures/paper-web`.
 */
export function supportedSchemas(): Set<string> {
  const parsed = JSON.parse(fs.readFileSync(siteAssetPath("reflowtex/supported-schemas.json"), "utf8")) as unknown;
  if (!Array.isArray(parsed) || parsed.some((entry) => typeof entry !== "string" || !/^[0-9a-f]{64}$/u.test(entry)))
    throw new Error("reflowtex/supported-schemas.json must be an array of sha256 hex strings");
  return new Set(parsed as string[]);
}

/** Strip a converter's own content-hash rename, then re-hash uniformly:
 * `cmmi10.reflowtex-76a9a304.otf` → `cmmi10.<hash12>.otf`. */
function hashedFontName(original: string, bytes: Buffer): string {
  const dot = original.lastIndexOf(".");
  const extension = original.slice(dot);
  const stem = original.slice(0, dot).replace(/\.reflowtex-[0-9a-f]{8}$/u, "");
  return `${stem}.${createHash("sha256").update(bytes).digest("hex").slice(0, 12)}${extension}`;
}

/**
 * Gate and unpack one submission's bundle for its paper page. Returns
 * undefined — and logs why — when the page must stay PDF-only: no bundle
 * attached, or a schema/tool/format this viewer does not support. Corruption
 * (cache bytes not matching the record, a tar or index that fails its own
 * checks, record/bundle skew) throws with the record named, like every other
 * corrupt-record path.
 */
export function preparePaperWeb(
  submission: SiteSubmission,
  log: (line: string) => void,
): PreparedPaperWeb | undefined {
  const id = submission.record.id;
  const web = submission.output?.paper?.web;
  if (!web || !submission.bundleFile || !submission.paperFile) return undefined;

  // The gate reads only the record, so an unsupported bundle is never even
  // opened — one schema bump must not break old paper pages at deploy time.
  if (web.format.tool !== SUPPORTED_TOOL) {
    log(`${id}: paper web bundle was derived by ${web.format.tool}, not ${SUPPORTED_TOOL}; rendering the PDF-only page`);
    return undefined;
  }
  if (!supportedSchemas().has(web.format.schema)) {
    log(`${id}: paper web schema ${web.format.schema.slice(0, 12)} is not supported by the vendored viewer; rendering the PDF-only page`);
    return undefined;
  }

  const bytes = fs.readFileSync(submission.bundleFile);
  const digest = createHash("sha256").update(bytes).digest("hex");
  if (digest !== web.bundle.digest || bytes.length !== web.bundle.bytes)
    throw new Error(`${id} cached web bundle does not match its record (digest ${digest}, ${bytes.length} bytes)`);

  let bundle;
  try {
    bundle = readPaperBundle(bytes);
  } catch (error) {
    throw new Error(`${id} paper web bundle is invalid: ${(error as Error).message}`);
  }
  if (bundle.index.schema !== web.format.schema || bundle.index.rev !== web.format.rev || bundle.index.tool !== web.format.tool)
    throw new Error(`${id} paper web bundle index disagrees with the record's format pin`);
  if (bundle.index.formatVersion !== SUPPORTED_FORMAT_VERSION) {
    log(`${id}: paper web bundle format v${bundle.index.formatVersion} is newer than this build understands; rendering the PDF-only page`);
    return undefined;
  }

  const files: Array<[string, Buffer]> = [];
  const fontMap: Record<string, string> = {};
  for (const original of Object.keys(bundle.index.fonts).sort()) {
    const fontBytes = bundle.files.get(bundle.index.fonts[original]!)!;
    const served = hashedFontName(original, fontBytes);
    fontMap[original] = served;
    files.push([`fonts/${served}`, fontBytes]);
  }

  const blockBytes = bundle.index.blocks.map((name) => bundle.files.get(name)!);
  const embeddedSize = blockBytes.reduce((sum, block) => sum + Math.ceil(block.length / 3) * 4, 0);
  const embed = embeddedSize <= EMBED_BUDGET_BYTES;
  const blocks = bundle.index.blocks.map((name, index) => {
    if (embed) return { b64: blockBytes[index]!.toString("base64") };
    const basename = name.slice("blocks/".length);
    files.push([`${id}/paper-web/${basename}`, blockBytes[index]!]);
    return { src: `paper-web/${basename}` };
  });

  return {
    page: {
      schemaB64: bundle.files.get("schema/latex.proto")!.toString("base64"),
      fontMap,
      blocks,
    },
    files,
  };
}
