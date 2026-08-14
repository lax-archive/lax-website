import crypto from "node:crypto";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const REQUIRED_FILES = [
  "package.json",
  "dist/sitegen/generate.js",
  "dist/sitegen/assets.js",
  "assets/site/",
  "content/landing.md",
  "content/contributing.md",
];

function archiveFiles(archive) {
  const listing = execFileSync("tar", ["-tzf", archive], { encoding: "utf8" });
  return listing
    .split("\n")
    .filter(Boolean)
    .map((entry) => {
      if (!entry.startsWith("package/")) {
        throw new Error(`renderer archive contains an entry outside package/: ${entry}`);
      }
      return entry.slice("package/".length);
    });
}

export function verifyRendererArchive(archive) {
  const files = archiveFiles(archive);
  for (const required of REQUIRED_FILES) {
    const present = required.endsWith("/")
      ? files.some((file) => file.startsWith(required))
      : files.includes(required);
    if (!present) throw new Error(`renderer archive is missing ${required}`);
  }
}

function sha256(file) {
  return crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex");
}

function packRenderer(repositoryRoot, destination) {
  const staging = fs.mkdtempSync(path.join(destination, ".package-renderer-"));
  try {
    const output = execFileSync(
      "npm",
      ["pack", "--json", "--pack-destination", staging],
      { cwd: repositoryRoot, encoding: "utf8", stdio: ["ignore", "pipe", "inherit"] },
    );
    const results = JSON.parse(output);
    const filename = results[0]?.filename;
    if (results.length !== 1 || typeof filename !== "string" || path.basename(filename) !== filename) {
      throw new Error("npm pack did not produce exactly one renderer archive");
    }
    return path.join(staging, filename);
  } catch (error) {
    fs.rmSync(staging, { recursive: true, force: true });
    throw error;
  }
}

export function packageRenderer(commit, outputDirectory, repositoryRoot = process.cwd()) {
  if (!/^[0-9a-f]{40}$/u.test(commit)) {
    throw new Error("renderer commit must be a full lowercase Git commit SHA");
  }

  const destination = path.resolve(outputDirectory);
  const archive = path.join(destination, `${commit}.tgz`);
  fs.mkdirSync(destination, { recursive: true });

  const reused = fs.existsSync(archive);
  if (!reused) {
    const packed = packRenderer(path.resolve(repositoryRoot), destination);
    try {
      verifyRendererArchive(packed);
      fs.renameSync(packed, archive);
    } finally {
      fs.rmSync(path.dirname(packed), { recursive: true, force: true });
    }
  }

  verifyRendererArchive(archive);
  const metadata = {
    commit,
    tarball: `${commit}.tgz`,
    sha256: sha256(archive),
  };
  fs.writeFileSync(path.join(destination, "latest.json"), `${JSON.stringify(metadata, null, 2)}\n`);
  return { ...metadata, archive, reused };
}

function main() {
  const [commit, outputDirectory] = process.argv.slice(2);
  if (commit === undefined || outputDirectory === undefined || process.argv.length !== 4) {
    console.error("usage: package-renderer.mjs <commit-sha> <output-directory>");
    process.exitCode = 2;
    return;
  }
  const result = packageRenderer(commit, outputDirectory);
  console.log(
    `${result.reused ? "Reused" : "Packaged"} renderer ${result.commit} (${result.sha256}).`,
  );
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) main();
