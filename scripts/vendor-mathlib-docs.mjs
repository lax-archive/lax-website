// Run with a downloaded declaration-data.bmp. The vendored input is never
// served to browsers; only the links actually used enter generated HTML.
import fs from "node:fs";
import { createHash } from "node:crypto";
import { gzipSync } from "node:zlib";

const input = process.argv[2];
if (!input) throw new Error("usage: node scripts/vendor-mathlib-docs.mjs declaration-data.bmp");
const source = fs.readFileSync(input);
const data = JSON.parse(source);
const entries = Object.entries(data.declarations).filter(([, entry]) =>
  typeof entry.docLink === "string" && /^\.\/(?:Mathlib|Init|Std|Lean)\//u.test(entry.docLink))
  .map(([name, entry]) => [name, entry.docLink]).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
if (!entries.length) throw new Error("index contains no Mathlib declarations");
const compressed = gzipSync(JSON.stringify(Object.fromEntries(entries)), { level: 9 });
const sha256 = (bytes) => createHash("sha256").update(bytes).digest("hex");
const directory = new URL("../assets/mathlib-docs/", import.meta.url);
fs.mkdirSync(directory, { recursive: true });
fs.writeFileSync(new URL("declarations.json.gz", directory), compressed);
fs.writeFileSync(new URL("snapshot.json", directory), JSON.stringify({
  source: "https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp",
  sourceSha256: sha256(source), sha256: sha256(compressed), declarations: entries.length,
}, null, 2) + "\n");
