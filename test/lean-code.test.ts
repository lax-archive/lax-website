import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { LeanHoverClient, hoverType } from "../src/lean-code-host.js";
import { highlightSource } from "../src/sitegen/highlight.js";
import { leanCodeInputs, liveLeanCode, liveLeanLink, loadLeanCode, parseLeanCode } from "../src/sitegen/lean-code.js";
import { SiteModel, type SiteSubmission } from "../src/sitegen/model.js";
import { landingLeanModel } from "../src/sitegen/pages/index.js";
import { sourceTypeLinks } from "../src/sitegen/source-links.js";
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
    const base = model.conceptHome.get("Lax1.Base")!.concept;
    base.statements = [{ id: "Lax1.double", signature: "double (n : Nat) : Nat" }];
    const main = model.conceptHome.get("Lax1.Main")!.concept;
    const constant = main.sourceText.indexOf("double"), variable = main.sourceText.lastIndexOf("n");
    const prepared = { version: 1, digest: leanCodeInputs(model, "Lax1.Main").digest, hovers: [
      { start: constant, end: constant + 6, text: "Lax1.double (n : Nat) : Nat" },
      { start: variable, end: variable + 1, text: "n : Nat" },
    ] };
    const cache = tmpDir("lax-hover-statements-");
    fs.writeFileSync(path.join(cache, `${prepared.digest}.json`), JSON.stringify(prepared));
    loadLeanCode(model, cache);
    expect(model.leanCode.get("Lax1.Main")!.hovers).toEqual([prepared.hovers[1]]);
  });
  it("preserves syntax, Unicode, identifier navigation and source lines with type hovers", async () => {
    const source = "def α := α\n-- $x$";
    const html = await highlightSource(source, [], new Set(), {
      links: [{ start: 9, end: 10, href: "../lax-1/Lax1.Base.html#L1" }],
      hovers: [{ start: 4, end: 5, text: 'α : Nat <script>"' }, { start: 9, end: 10, text: "α : Nat" }],
    });
    expect(html).toContain('tabindex="0" data-lean-type="α : Nat &lt;script&gt;&quot;"');
    expect(html).toContain('href="../lax-1/Lax1.Base.html#L1" data-lean-type="α : Nat"');
    expect(html.match(/data-lean-type=/g)).toHaveLength(2);
    expect(html).not.toContain("title="); expect(html).not.toContain("<script>");
    expect(html).toContain('id="L2"'); expect(html).toContain('class="katex"');
    const annotated = "def f (x /- explicit type -/ : Nat) := x";
    const binder = annotated.indexOf("x"), use = annotated.lastIndexOf("x"), type = annotated.indexOf("Nat");
    const typed = await highlightSource(annotated, [], new Set(), { hovers: [
      { start: binder, end: binder + 1, text: "x : Nat" },
      { start: type, end: type + 3, text: "Nat : Type" },
      { start: use, end: use + 1, text: "x : Nat" },
    ] });
    expect(typed.match(/data-lean-type="x : Nat"/g)).toHaveLength(1);
    expect(typed).toContain('data-lean-type="Nat : Type"');
    expect(typed.indexOf('data-lean-type="x : Nat"')).toBeGreaterThan(typed.indexOf("explicit type"));
    const model = fixture(), signature = "x : Lax1.double Nat";
    const links = sourceTypeLinks(model, "Lax1.Main", "../", signature);
    expect(links.map(link => signature.slice(link.start, link.end))).toEqual(["Lax1.double", "Nat"]);
    expect(links[0]!.href).toBe("../lax-1/Lax1.Base.html#L4");
    expect(links[1]!.href).toContain("/mathlib4_docs/Init/Prelude.html#Nat");
    expect(sourceTypeLinks(model, "Lax1.Main", "../", "n : ℕ").map(link => link.href)).toEqual([links[1]!.href]);
    const nonnegative = sourceTypeLinks(model, "Lax1.Main", "../", "r : ℝ≥0");
    expect(nonnegative).toHaveLength(1);
    expect(nonnegative[0]!.end - nonnegative[0]!.start).toBe(3);
    expect(nonnegative[0]!.href).toContain("#NNReal");
    expect(sourceTypeLinks(model, "Lax1.Main", "../", "f (Nat : Type) : Nat")).toEqual([]);
    const linkedType = await highlightSource("def x := 0", [], new Set(), {
      hovers: [{ start: 4, end: 5, text: signature }],
      typeLinks: text => sourceTypeLinks(model, "Lax1.Main", "../", text),
    });
    expect(linkedType).toContain('role="button"');
    expect(linkedType).toContain('data-lean-type-links="');
    expect(linkedType).toContain("../lax-1/Lax1.Base.html#L4");
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
