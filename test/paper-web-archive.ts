// The shared paper-web test archive: one submission (lax-21) whose paper
// mirrors the committed fixture bundle — its four marks are the fixture's
// mark table, so the viewer's m1..m4 anchors join real cards.

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import type { SiteSubmission } from "../src/sitegen/model.js";
import type { PaperWebEntry } from "../src/types.js";
import { tmpDir } from "./helpers.js";

export const FIXTURE_DIR = path.join("test", "fixtures", "paper-web");
export const FIXTURE_TAR = path.join(FIXTURE_DIR, "paper-web.tar");
export const fixtureRecord = JSON.parse(fs.readFileSync(path.join(FIXTURE_DIR, "paper-web.json"), "utf8")) as {
  web: PaperWebEntry;
  marks: { n: number; id: string; kind: string }[];
};

export const pdf = Buffer.from("%PDF-1.7\n% a stand-in for the compiled paper\n");
export const pdfDigest = createHash("sha256").update(pdf).digest("hex");
const source = { repository: "https://github.com/example/spike.git", commit: "a".repeat(40), folder: "." };

const point = (page: number, y: number, mode: "v" | "h" = "v") => ({ page, x: 72, y, mode });

/** lax-21 mirrors the fixture: its paper marks the fixture's four ids. */
export function webArchive(web: PaperWebEntry = fixtureRecord.web): SiteSubmission[] {
  return [{
    record: { specVersion: "1", id: "lax-21", state: "registered", createdAt: "2026-09-01T00:00:00Z", source },
    output: {
      specVersion: "1", id: "lax-21",
      manifest: { specVersion: "1", id: "lax-21", leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: "One and Zero", authors: [], bibEntries: [] },
      abstract: "The fixture paper.", requiredByConcepts: [], requiredByProofs: [],
      concepts: [
        { id: "Lax21.One", path: "concepts/Lax21/One.lean", title: "One", type: "definition", description: "The one.", imports: [], mathlibImports: [], sourceText: "", statements: [{ id: "Lax21.One.eq", signature: "eq : True" }] },
        { id: "Lax21.Zero", path: "concepts/Lax21/Zero.lean", title: "Zero", type: "definition", description: "The zero.", imports: [], mathlibImports: [], sourceText: "", statements: [{ id: "Lax21.Zero.eq", signature: "eq : True" }] },
      ],
      proofs: [
        { id: "Lax21Proofs.zero_eq", path: "proofs/Lax21Proofs/ZeroEq.lean", conclusion: "Lax21.Zero.eq", assumptions: [], description: "Direct." },
        { id: "Lax21Proofs.one_eq", path: "proofs/Lax21Proofs/OneEq.lean", conclusion: "Lax21.One.eq", assumptions: [], description: "Direct." },
      ],
      paper: {
        folder: "paper", main: "main.tex", engine: "lualatex",
        pdf: { digest: pdfDigest, bytes: pdf.length, pages: 1 },
        pageSizes: [[595.28, 841.89]],
        marks: fixtureRecord.marks.map((mark, index) => ({
          id: mark.id, kind: mark.kind as "concept" | "proof",
          begin: point(1, 700 - index * 100), end: point(1, 650 - index * 100),
        })),
        web,
      },
    },
  }];
}

export function attach(submissions: SiteSubmission[], options: { pdf?: boolean; bundle?: string } = {}): SiteSubmission[] {
  const paperFile = path.join(tmpDir("lax-paper-cache-"), `${pdfDigest}.pdf`);
  fs.writeFileSync(paperFile, pdf);
  return submissions.map((submission) => submission.output?.paper
    ? {
        ...submission,
        ...(options.pdf === false ? {} : { paperFile }),
        ...(options.bundle === undefined ? {} : { bundleFile: options.bundle }),
      }
    : submission);
}

/** The rendered-fixture archive: PDF stub and the committed bundle attached. */
export function attachFixturePaper(): SiteSubmission[] {
  return attach(webArchive(), { bundle: FIXTURE_TAR });
}
