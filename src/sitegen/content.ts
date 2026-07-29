import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const CONTENT_FILE = /^[a-z0-9][a-z0-9-]*\.md$/;

/** Read an editorial Markdown page from the repository's content directory. */
export function contentMarkdown(name: string): string {
  if (!CONTENT_FILE.test(name)) throw new Error(`invalid content filename: ${name}`);
  const file = path.join(
    path.dirname(fileURLToPath(import.meta.url)),
    "..",
    "..",
    "content",
    name,
  );
  return fs.readFileSync(file, "utf8").replace(/<!--[\s\S]*?-->/g, "");
}
