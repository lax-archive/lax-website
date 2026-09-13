import fs from "node:fs";
import path from "node:path";
import { expect, it, vi } from "vitest";
import { generateSite } from "../src/sitegen/generate.js";
import { tmpDir } from "./helpers.js";

it("keeps the previous site when asset packaging fails before replacement", async () => {
  const parent = tmpDir("lax-graph-atomic-"), output = path.join(parent, "site");
  fs.mkdirSync(output); fs.writeFileSync(path.join(output, "index.html"), "previous complete site");
  const copy = vi.spyOn(fs, "cpSync").mockImplementation(() => { throw new Error("simulated disk write failure"); });
  try {
    await expect(generateSite([], output)).rejects.toThrow("simulated disk write failure");
    expect(fs.readFileSync(path.join(output, "index.html"), "utf8")).toBe("previous complete site");
    expect(fs.readdirSync(parent)).toEqual(["site"]);
  } finally { copy.mockRestore(); }
});
