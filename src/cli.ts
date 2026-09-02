import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { loadSubmissions, submissionsMissingPapers } from "./database.js";
import { fetchPapers } from "./papers.js";
import { SITE_MIME } from "./sitegen/assets.js";
import { generateSite } from "./sitegen/generate.js";

type Command = "build" | "serve" | "fetch-papers";

function option(name: string, fallback: string): string {
  const index = process.argv.indexOf(name);
  if (index === -1) return fallback;
  const value = process.argv[index + 1];
  if (!value || value.startsWith("--"))
    throw new Error(`${name} requires a value`);
  return value;
}

function flag(name: string): boolean {
  return process.argv.includes(name);
}

function numberOption(name: string, fallback: number): number {
  const value = Number(option(name, String(fallback)));
  if (!Number.isInteger(value) || value < 1 || value > 65_535)
    throw new Error(`${name} must be an integer between 1 and 65535`);
  return value;
}

const command = (process.argv[2] ?? "build") as Command;
if (command !== "build" && command !== "serve" && command !== "fetch-papers")
  throw new Error("usage: npm run site:build|site:serve|papers:fetch -- [--database DIR] [--papers DIR] [--no-papers] [--out DIR] [--port N]");

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const databaseDir = path.resolve(option("--database", path.join(root, "data", "lax-db")));
const papersDir = path.resolve(option("--papers", path.join(root, "data", "papers")));
// Previews carry no PDFs (the gh-pages branch keeps every deployment's full
// tree); production must have every paper the database references.
const withPapers = !flag("--no-papers");
const outDir = path.resolve(option("--out", path.join(root, "_site")));

async function build(): Promise<void> {
  const submissions = loadSubmissions(databaseDir, withPapers ? { papersDir } : {});
  if (withPapers) {
    const missing = submissionsMissingPapers(submissions);
    if (missing.length)
      throw new Error(`papers cache ${papersDir} lacks the PDF of ${missing.map((s) => s.record.id).join(", ")}; run \`npm run papers:fetch\` or build with --no-papers`);
  }
  await generateSite(submissions, outDir);
  console.log(`generated ${submissions.length} archive records in ${outDir}`);
}

if (command === "fetch-papers") {
  const fetched = await fetchPapers(loadSubmissions(databaseDir), papersDir, { log: (line) => console.log(line) });
  console.log(`papers cache ${papersDir}: ${fetched.length} fetched`);
} else if (command === "build") {
  await build();
} else {
  const port = numberOption("--port", 3000);
  let timer: NodeJS.Timeout | undefined;
  let building = false;
  let buildAgain = false;

  const rebuild = async () => {
    if (building) {
      buildAgain = true;
      return;
    }
    building = true;
    try {
      await build();
    } catch (error) {
      console.error(`site rebuild failed: ${(error as Error).message}`);
    } finally {
      building = false;
      if (buildAgain) {
        buildAgain = false;
        void rebuild();
      }
    }
  };

  const schedule = () => {
    clearTimeout(timer);
    timer = setTimeout(() => void rebuild(), 200);
  };

  await build();
  fs.watch(databaseDir, { recursive: true }, schedule);
  fs.watch(path.join(root, "content"), { recursive: true }, schedule);
  fs.watch(path.join(root, "assets"), { recursive: true }, schedule);

  http.createServer((request, response) => {
    const url = new URL(request.url ?? "/", "http://localhost");
    let relative = decodeURIComponent(url.pathname).replace(/^\/+/, "");
    if (relative === "" || relative.endsWith("/")) relative += "index.html";
    const file = path.resolve(outDir, relative);
    const inside = file === outDir || file.startsWith(`${outDir}${path.sep}`);
    if (!inside || !fs.existsSync(file) || fs.statSync(file).isDirectory()) {
      response.writeHead(404, { "content-type": "text/plain; charset=utf-8" });
      response.end("not found");
      return;
    }
    response.writeHead(200, {
      "content-type": SITE_MIME[path.extname(file)] ?? "application/octet-stream",
    });
    response.end(fs.readFileSync(file));
  }).listen(port, () => {
    console.log(`preview: http://localhost:${port}/`);
  });
}
