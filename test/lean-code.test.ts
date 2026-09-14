import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { LeanHoverClient, hoverType } from "../src/lean-code-host.js";
import { highlightSource } from "../src/sitegen/highlight.js";
import { leanCodeInputs, liveLeanCode, liveLeanLink, loadLeanCode, parseLeanCode } from "../src/sitegen/lean-code.js";
import { SiteModel, type SiteSubmission } from "../src/sitegen/model.js";
import { landingLeanModel } from "../src/sitegen/pages/index.js";
import { tmpDir } from "./helpers.js";

function fixture(): SiteModel {
  const submission: SiteSubmission = {
    record: { specVersion: "1", id: "lax-1", state: "registered", createdAt: "2026-09-14" },
    output: { specVersion: "1", id: "lax-1", abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
      manifest: { specVersion: "1", id: "lax-1", title: "Test", authors: [{ name: "Hidden Author" }], bibEntries: [],
        anonymous: true, leanVersion: "v4.33.0", mathlibVersion: "a".repeat(40) },
      concepts: [
        { id: "Lax1.Base", path: "Lax1/Base.lean", title: "Base", type: "definition", description: "", imports: [], statements: [],
          sourceText: "import Mathlib.Data.Nat.Basic\n/-! Hidden Author -/\nnamespace Lax1\ndef double (n : Nat) := n + n\nend Lax1\n" },
        { id: "Lax1.Main", path: "Lax1/Main.lean", title: "Main", type: "definition", description: "", imports: ["Lax1.Base"], statements: [],
          sourceText: "import Lax1.Base\nopen Lax1\ndef twice (n : Nat) := double n\n" },
      ],
    },
  };
  return new SiteModel([submission]);
}

describe("prepared Lean information", () => {
  it("keeps only the compiler's Lean signature, never documentation or Markdown", () => {
    expect(hoverType({ contents: { kind: "markdown", value: "```lean\nx : List α\n```\nHidden Author [link](https://example.com)" } })).toBe("x : List α");
    expect(hoverType({ contents: { kind: "markdown", value: "A docstring with ```lean\nfake\n```" } })).toBeUndefined();
  });
  it("invalidates source/dependency changes and rejects stale, overlapping or non-token ranges", () => {
    const model = fixture(), original = leanCodeInputs(model, "Lax1.Main");
    expect(original.modules).toEqual(["Lax1.Base", "Lax1.Main"]);
    model.conceptHome.get("Lax1.Base")!.concept.sourceText += "\ndef extra := 0\n";
    expect(leanCodeInputs(model, "Lax1.Main").digest).not.toBe(original.digest);
    const data = { version: 1, digest: "digest", hovers: [{ start: 4, end: 5, text: "x : Nat" }] };
    expect(parseLeanCode(JSON.stringify(data), "digest", "def x := 1").hovers).toEqual(data.hovers);
    expect(() => parseLeanCode(JSON.stringify(data), "stale", "def x := 1")).toThrow();
    expect(() => parseLeanCode(JSON.stringify(data), "digest", "--  x   ")).toThrow();
    expect(() => parseLeanCode(JSON.stringify({ ...data, hovers: [...data.hovers, ...data.hovers] }), "digest", "def x := 1")).toThrow();
    expect(() => loadLeanCode(model, tmpDir("lax-hover-missing-"), true)).toThrow(/lean:prepare/);
  });
  it("preserves syntax, Unicode, identifier navigation and source lines without native titles", async () => {
    const source = "def α := α\n-- $x$";
    const html = await highlightSource(source, [], new Set(), {
      links: [{ start: 9, end: 10, href: "../lax-1/Lax1.Base.html#L1" }],
      hovers: [{ start: 4, end: 5, text: "α : Nat" }, { start: 9, end: 10, text: 'α : Nat <script>"' }],
    });
    expect(html).toContain('tabindex="0" data-lean-type="α : Nat"');
    expect(html).toContain('href="../lax-1/Lax1.Base.html#L1" data-lean-type="α : Nat &lt;script&gt;&quot;"');
    expect(html).not.toContain("title="); expect(html).not.toContain("<script>");
    expect(html).toContain('id="L2"'); expect(html).toContain('class="katex"');
  });
  it("exports dependencies in order with scoped commands and no anonymous annotations", () => {
    const model = fixture(), source = liveLeanCode(model, "Lax1.Main")!;
    expect(source).not.toContain("import Lax1.Base");
    expect(source).toContain("import Mathlib.Data.Nat.Basic");
    expect(source.indexOf("def double")).toBeLessThan(source.indexOf("def twice"));
    expect(source).not.toContain("Hidden Author");
    expect(source.match(/^section$/gm)).toHaveLength(2);
    expect(liveLeanLink(model, "Lax1.Main")).toContain("#project=mathlib-stable&amp;code=");
    model.conceptHome.get("Lax1.Main")!.concept.sourceText += "private def secret := 0\n";
    expect(liveLeanCode(model, "Lax1.Main")).toBeUndefined();
  });
  it("includes the landing examples in preparation without treating them as archive records", () => {
    const examples = landingLeanModel();
    expect(examples.conceptHome.has("Primes")).toBe(true);
    expect(liveLeanCode(examples, "PrimeDivisor")).toContain("def Prime");
    expect(liveLeanCode(examples, "PrimeDivisor")).not.toContain("import Primes");
  });
});

it.runIf(Boolean(process.env.LEAN_HOVER_TEST_BIN))("uses Lean's inferred types for implicit binders, Unicode and shadowed variables", async () => {
  const root = tmpDir("lax-hover-compiler-");
  const source = "def identity {α : Type} (x : α) : α := x\ndef shadow (x : Nat) : Bool :=\n  let x := true\n  x\n";
  const file = path.join(root, "Example.lean"); fs.writeFileSync(file, source);
  const client = new LeanHoverClient(process.env.LEAN_HOVER_TEST_BIN!, root, root);
  await client.initialize();
  try {
    const hovers = await client.hovers(file, source);
    expect(hovers.filter(h => source.slice(h.start, h.end) === "x").map(h => h.text)).toEqual(expect.arrayContaining(["x : α", "x : Nat", "x : Bool"]));
    expect(hovers.some(h => h.text === "α : Type")).toBe(true);
  } finally { await client.close(); }
}, 120_000);
