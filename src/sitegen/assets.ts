import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const SITE_ASSET_DIR = fileURLToPath(new URL("../../assets/site", import.meta.url));

export const SITE_MIME: Record<string, string> = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".pdf": "application/pdf",
  ".svg": "image/svg+xml",
  ".woff2": "font/woff2",
  // The reflow paper surface: its per-paper OTF/TTF fonts, the protobuf
  // block files pages over the embed budget fetch, and the wire schema.
  ".otf": "font/otf",
  ".ttf": "font/ttf",
  ".pb": "application/octet-stream",
  ".proto": "text/plain; charset=utf-8",
  ".txt": "text/plain; charset=utf-8",
};

/** Resolve a bundled browser asset without exposing the package layout. */
export function siteAssetPath(relative: string): string {
  const file = path.resolve(SITE_ASSET_DIR, relative);
  if (file !== SITE_ASSET_DIR && !file.startsWith(`${SITE_ASSET_DIR}${path.sep}`))
    throw new Error(`site asset escapes the asset directory: ${relative}`);
  return file;
}

/**
 * Browser assets that ship from npm packages rather than `assets/site/`:
 * site-relative path → module specifier. KaTeX is the one; pdf.js is
 * vendored into `assets/site/pdfjs/` instead (scripts/vendor-pdfjs.mjs)
 * so the renderer tarball authors install stays self-contained.
 */
const PACKAGED_ASSETS: Record<string, string> = {
  "katex.css": "katex/dist/katex.min.css",
};

function packagedAssetSource(relative: string): string {
  return createRequire(import.meta.url).resolve(PACKAGED_ASSETS[relative]!);
}

/** Stable content fingerprint for cache-busting a bundled browser asset. */
export function siteAssetVersion(relative: string): string {
  const file = relative in PACKAGED_ASSETS ? packagedAssetSource(relative) : siteAssetPath(relative);
  return createHash("sha256").update(fs.readFileSync(file)).digest("hex").slice(0, 12);
}

export function copyAssets(outDir: string): void {
  const target = path.join(outDir, "assets");
  fs.mkdirSync(target, { recursive: true });
  fs.cpSync(SITE_ASSET_DIR, target, { recursive: true });

  for (const relative of Object.keys(PACKAGED_ASSETS)) {
    const destination = path.join(target, relative);
    fs.mkdirSync(path.dirname(destination), { recursive: true });
    fs.copyFileSync(packagedAssetSource(relative), destination);
  }
  const katexDir = path.dirname(packagedAssetSource("katex.css"));
  const fontTarget = path.join(target, "fonts");
  fs.mkdirSync(fontTarget, { recursive: true });
  for (const file of fs.readdirSync(path.join(katexDir, "fonts")).filter((name) => name.endsWith(".woff2")).sort())
    fs.copyFileSync(path.join(katexDir, "fonts", file), path.join(fontTarget, file));
}
