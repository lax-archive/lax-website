// Copy the pdf.js build the paper viewer runs on from the pinned
// `pdfjs-dist` dev dependency into assets/site/pdfjs/. The bytes are
// committed: the renderer tarball `lax serve` installs is built from
// `assets/` and `dist/` alone, and pulling pdfjs-dist (with its optional
// native canvas) onto every author's machine would cost far more than the
// 1.7 MB vendored here. Bump the dev dependency, run `npm run pdfjs:vendor`,
// commit; test/paper.test.ts fails while the two drift apart.
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const target = fileURLToPath(new URL("../assets/site/pdfjs/", import.meta.url));

export const VENDORED_PDFJS = {
  "pdf.min.mjs": "pdfjs-dist/build/pdf.min.mjs",
  "pdf.worker.min.mjs": "pdfjs-dist/build/pdf.worker.min.mjs",
  "LICENSE.txt": "pdfjs-dist/LICENSE",
};

export function vendorPdfjs() {
  fs.mkdirSync(target, { recursive: true });
  for (const [name, specifier] of Object.entries(VENDORED_PDFJS))
    fs.copyFileSync(require.resolve(specifier), path.join(target, name));
  const { version } = require("pdfjs-dist/package.json");
  fs.writeFileSync(path.join(target, "VERSION.txt"), `${version}\n`);
  return version;
}

if (process.argv[1] && import.meta.url === new URL(`file://${path.resolve(process.argv[1])}`).href)
  console.log(`vendored pdf.js ${vendorPdfjs()} into ${target}`);
