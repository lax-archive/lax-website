import fs from "node:fs";
import os from "node:os";
import path from "node:path";

export function tmpDir(prefix = "lax-website-test-"): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), prefix));
}
