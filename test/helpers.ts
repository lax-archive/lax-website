import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll } from "vitest";

const temporaryDirectories: string[] = [];
afterAll(() => {
  if (process.env.LAX_KEEP_TEST_OUTPUT === "1") return;
  for (const directory of temporaryDirectories) fs.rmSync(directory, { recursive: true, force: true });
});

export function tmpDir(prefix = "lax-website-test-"): string {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), prefix));
  temporaryDirectories.push(directory);
  return directory;
}
