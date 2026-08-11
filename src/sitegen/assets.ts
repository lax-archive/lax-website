import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const SITE_ASSET_DIR = fileURLToPath(new URL("../../assets/site", import.meta.url));

export const SITE_MIME: Record<string, string> = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".pdf": "application/pdf",
  ".svg": "image/svg+xml",
  ".woff2": "font/woff2",
  ".txt": "text/plain; charset=utf-8",
};

/** Resolve a bundled browser asset without exposing the package layout. */
export function siteAssetPath(relative: string): string {
  const file = path.resolve(SITE_ASSET_DIR, relative);
  if (file !== SITE_ASSET_DIR && !file.startsWith(`${SITE_ASSET_DIR}${path.sep}`))
    throw new Error(`site asset escapes the asset directory: ${relative}`);
  return file;
}

export function copyAssets(outDir: string): void {
  const target = path.join(outDir, "assets");
  fs.mkdirSync(target, { recursive: true });
  fs.cpSync(SITE_ASSET_DIR, target, { recursive: true });

  const require = createRequire(import.meta.url);
  const katexDir = path.dirname(require.resolve("katex/dist/katex.min.css"));
  fs.copyFileSync(path.join(katexDir, "katex.min.css"), path.join(target, "katex.css"));
  const fontTarget = path.join(target, "fonts");
  fs.mkdirSync(fontTarget, { recursive: true });
  for (const file of fs.readdirSync(path.join(katexDir, "fonts")).filter((name) => name.endsWith(".woff2")).sort())
    fs.copyFileSync(path.join(katexDir, "fonts", file), path.join(fontTarget, file));
}
