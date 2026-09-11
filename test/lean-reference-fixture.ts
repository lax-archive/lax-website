import fs from "node:fs";
import { parseLeanReferences } from "../src/lean-references.js";
import type { SiteSubmission } from "../src/sitegen/model.js";

export const referenceModule = "Lax17.Fields";
export const referenceSource = fs.readFileSync("test/fixtures/lean-references/Lax17/Fields.lean", "utf8");
export const referenceMetadata = fs.readFileSync("test/fixtures/lean-references/Fields.ilean.json");

export function referenceSubmission(): SiteSubmission {
  return {
    record: { id: "lax-17", specVersion: "1", state: "registered", createdAt: "2026-09-09T00:00:00Z" },
    output: { id: "lax-17", specVersion: "1",
      manifest: { id: "lax-17", specVersion: "1", leanVersion: "v4.30.0", mathlibVersion: "abc", title: "Fields", authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
      concepts: [{ id: referenceModule, path: "concepts/Lax17/Fields.lean", title: "Fields", type: "definition", description: "", imports: [], statements: [], sourceText: referenceSource }],
    },
    sourceReferences: new Map([[referenceModule, parseLeanReferences(referenceMetadata.toString("utf8"), referenceModule, referenceSource)]]),
  };
}
