import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

export const INTEGRITY_FILE = "lax-integrity.json";

function sha256(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function siteFiles(root) {
  const files = [];
  const walk = (directory) => {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
      if (entry.name === ".git") continue;
      const file = path.join(directory, entry.name);
      if (entry.isDirectory()) walk(file);
      else {
        const relative = path.relative(root, file).split(path.sep).join("/");
        if (relative === INTEGRITY_FILE) continue;
        const bytes = fs.readFileSync(file);
        files.push({ path: relative, bytes: bytes.length, sha256: sha256(bytes) });
      }
    }
  };
  walk(root);
  return files.sort((a, b) => a.path.localeCompare(b.path));
}

function commit(value, label) {
  if (!/^[0-9a-f]{40}$/.test(value)) throw new Error(`${label} must be a lowercase 40-character Git commit`);
  return value;
}

/** Seal one generated site with exact source revisions and hashes of every
 * output file. The manifest itself is deterministic and can be compared byte
 * for byte with the public endpoint. */
export function writeIntegrityManifest(siteRoot, websiteCommit, databaseCommit) {
  const root = path.resolve(siteRoot);
  if (!fs.existsSync(root) || !fs.statSync(root).isDirectory())
    throw new Error(`site directory does not exist: ${root}`);
  const files = siteFiles(root);
  const treeDigest = sha256(Buffer.from(files.map((file) => `${file.path}\0${file.bytes}\0${file.sha256}\n`).join("")));
  const manifest = {
    formatVersion: 1,
    websiteCommit: commit(websiteCommit, "website commit"),
    databaseCommit: commit(databaseCommit, "database commit"),
    treeDigest,
    files,
  };
  fs.writeFileSync(path.join(root, INTEGRITY_FILE), `${JSON.stringify(manifest, null, 2)}\n`);
  return manifest;
}

function delay(milliseconds) {
  return new Promise((resolve) => setTimeout(resolve, milliseconds));
}

async function fetchBytes(url) {
  const response = await fetch(url, { signal: AbortSignal.timeout(15_000), cache: "no-store" });
  if (!response.ok) throw new Error(`${response.status} ${response.statusText}`);
  return Buffer.from(await response.arrayBuffer());
}

async function verifyFiles(files, baseUrl, nonce, attempt) {
  const failures = [];
  let cursor = 0;
  const workers = Array.from({ length: Math.min(8, files.length) }, async () => {
    while (cursor < files.length) {
      const file = files[cursor++];
      try {
        const url = new URL(file.path, baseUrl);
        url.searchParams.set("integrity", `${nonce}-${attempt}`);
        const bytes = await fetchBytes(url);
        if (bytes.length !== file.bytes || sha256(bytes) !== file.sha256) failures.push(file.path);
      } catch {
        failures.push(file.path);
      }
    }
  });
  await Promise.all(workers);
  return failures.sort();
}

/** Wait for the public CDN to serve the exact manifest, then independently
 * hash every rendered HTML page through a unique cache key. */
export async function verifyIntegritySite(manifestFile, siteUrl, nonce) {
  const local = fs.readFileSync(manifestFile);
  const manifest = JSON.parse(local.toString("utf8"));
  if (manifest.formatVersion !== 1 || !Array.isArray(manifest.files))
    throw new Error("invalid local site integrity manifest");
  const baseUrl = new URL(siteUrl.endsWith("/") ? siteUrl : `${siteUrl}/`);
  let manifestLive = false;
  for (let attempt = 1; attempt <= 100; attempt++) {
    try {
      const url = new URL(INTEGRITY_FILE, baseUrl);
      url.searchParams.set("integrity", `${nonce}-${attempt}`);
      if ((await fetchBytes(url)).equals(local)) {
        manifestLive = true;
        console.log(`integrity manifest live after ${attempt} probes`);
        break;
      }
    } catch {
      // Pages may return 404 while a deployment is propagating.
    }
    console.log(`probe ${attempt}: integrity manifest differs`);
    await delay(15_000);
  }
  if (!manifestLive) throw new Error(`site never served integrity manifest ${manifest.treeDigest}`);

  let pending = manifest.files.filter((file) => file.path.endsWith(".html"));
  for (let attempt = 1; attempt <= 20 && pending.length; attempt++) {
    pending = await verifyFiles(pending, baseUrl, nonce, attempt);
    if (!pending.length) break;
    console.log(`page verification ${attempt}: ${pending.length} page(s) differ`);
    await delay(5_000);
  }
  if (pending.length)
    throw new Error(`public pages differ from sealed tree: ${pending.slice(0, 20).join(", ")}${pending.length > 20 ? " …" : ""}`);
  console.log(`verified ${manifest.files.filter((file) => file.path.endsWith(".html")).length} public HTML pages`);
}

async function main() {
  const [command, ...args] = process.argv.slice(2);
  if (command === "write" && args.length === 3) writeIntegrityManifest(...args);
  else if (command === "verify" && args.length === 3) await verifyIntegritySite(...args);
  else {
    console.error("usage: site-integrity.mjs write <site-root> <website-commit> <database-commit> | verify <manifest-file> <site-url> <nonce>");
    process.exitCode = 2;
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) await main();
