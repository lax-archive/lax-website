import { describe, expect, it, vi } from "vitest";
import { highlightSource } from "../src/sitegen/highlight.js";
import { leanDeclarations, scanLeanSource } from "../src/sitegen/lean-source.js";
import { SiteModel, type SiteSubmission } from "../src/sitegen/model.js";
import { sourceLinks } from "../src/sitegen/source-links.js";
import type { ConceptEntry } from "../src/types.js";

function concept(id: string, sourceText: string, imports: string[] = []): ConceptEntry {
  return { id, sourceText, imports, path: `concepts/${id}.lean`, title: id, type: "definition", description: "", statements: [] };
}

function archive(concepts: ConceptEntry[]): SiteModel {
  const submission: SiteSubmission = {
    record: { specVersion: "1", id: "lax-17", state: "registered", createdAt: "2026-01-01T00:00:00Z" },
    output: { specVersion: "1", id: "lax-17",
      manifest: { specVersion: "1", id: "lax-17", leanVersion: "v4.30.0", mathlibVersion: "abc", title: "Test", authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [], concepts, proofs: [] },
  };
  return new SiteModel([submission]);
}

function links(model: SiteModel, id: string) {
  const source = model.conceptHome.get(id)!.concept.sourceText;
  return sourceLinks(model, id, "../").map((link) => ({ text: source.slice(link.start, link.end), href: link.href }));
}

const strip = (html: string) => html.replace(/<[^>]*>/gu, "").replace(/&quot;/gu, '"')
  .replace(/&#39;/gu, "'").replace(/&lt;/gu, "<").replace(/&gt;/gu, ">").replace(/&amp;/gu, "&");
const renderedLinks = (html: string) => [...html.matchAll(/<a class="lean-identifier-link" href="([^"]+)">([^]*?)<\/a>/gu)]
  .map((match) => ({ href: match[1], text: strip(match[2]!) }));

describe("Lean source navigation", () => {
  it("links the reported treewidth/grid-minor references to their actual declarations", async () => {
    const tree = concept("Lax17.Treewidth", "namespace Lax17.Treewidth\nnoncomputable def treewidth : Nat := 0\nend Lax17.Treewidth");
    const grid = concept("Lax17.GridMinor", "namespace Lax17.GridMinor\ndef ContainsGridMinor : Prop := True\nend Lax17.GridMinor");
    const claim = concept("Lax17.PolynomialGridMinor", [
      "import Lax17.Treewidth", "import Lax17.GridMinor", "namespace Lax17.PolynomialGridMinor",
      "/-- The statement. -/", "axiom polynomial_grid_minor_eight_polylog :",
      "  0 ≤ Lax17.Treewidth.treewidth → Lax17.GridMinor.ContainsGridMinor", "end Lax17.PolynomialGridMinor",
    ].join("\n"), [tree.id, grid.id]);
    claim.statements = [{ id: `${claim.id}.polynomial_grid_minor_eight_polylog`, signature: "", startLine: 4, endLine: 6 }];
    const model = archive([claim, grid, tree]);
    const html = await highlightSource(claim.sourceText, claim.statements, new Set(), { links: sourceLinks(model, claim.id, "../") });
    expect(renderedLinks(html)).toEqual(expect.arrayContaining([
      { text: "Lax17.Treewidth.treewidth", href: "../lax-17/Lax17.Treewidth.html#L2" },
      { text: "Lax17.GridMinor.ContainsGridMinor", href: "../lax-17/Lax17.GridMinor.html#L2" },
      { text: "polynomial_grid_minor_eight_polylog", href: `../lax-17/${claim.id}.html#s-${claim.statements[0]!.id}` },
    ]));
    expect(html).toContain(`id="s-${claim.statements[0]!.id}"`);
  });

  it("uses declaration namespaces, nested sections, rooted names, and multiline modifiers", () => {
    const source = [
      "namespace Different", "section S", "namespace Inner", "@[", "  simp", "]",
      "noncomputable", "def thing : Nat := 0", "end Inner", "end S",
      "protected def other : Nat := 1", "def _root_.Root.value : Nat := 2", "end Different",
      "def global : Nat := 3",
    ].join("\n");
    const target = concept("Lax17.Module", source);
    const caller = concept("Lax17.Caller", "#check Different.Inner.thing\n#check Different.other\n#check Root.value\n#check Lax17.Module.thing", [target.id]);
    expect(leanDeclarations(scanLeanSource(source)).map((d) => d.name)).toEqual([
      ["Different", "Inner", "thing"], ["Different", "other"], ["Root", "value"], ["global"],
    ]);
    expect(links(archive([target, caller]), caller.id)).toEqual([
      { text: "Different.Inner.thing", href: "../lax-17/Lax17.Module.html#L4" },
      { text: "Different.other", href: "../lax-17/Lax17.Module.html#L11" },
      { text: "Root.value", href: "../lax-17/Lax17.Module.html#L12" },
    ]);
  });

  it("lands at the complete leading comments before attributes and modifiers", async () => {
    const target = concept("Lax17.Target", [
      "namespace Shared", "-- The public description.", "/-- A nested /- note -/ and more details.",
      "The second paragraph. -/", "@[", "  simp", "]", "noncomputable", "def thing := 0",
      "-- A statement's first comment.", "/-- Its docstring. -/", "axiom claim : True", "end Shared",
    ].join("\r\n"));
    target.statements = [{ id: "Shared.claim", signature: "claim : True", startLine: 11, endLine: 12 }];
    const caller = concept("Lax17.Caller", "#check Shared.thing\n#check Shared.claim", [target.id]);
    const model = archive([target, caller]);
    expect(links(model, caller.id)).toEqual([
      { text: "Shared.thing", href: "../lax-17/Lax17.Target.html#L2" },
      { text: "Shared.claim", href: "../lax-17/Lax17.Target.html#s-Shared.claim" },
    ]);
    const html = await highlightSource(target.sourceText, target.statements);
    expect(html).toMatch(/<tr id="L10"[^]*?<td class="line-code"><span class="statement-anchor" id="s-Shared.claim"><\/span>/u);
    expect(html.match(/id="s-Shared.claim"/gu)).toHaveLength(1);
  });

  it("does not use module docs, trailing comments, or comments before another command", () => {
    const source = [
      "/-! Module documentation. -/", "def first := 0 -- trailing comment",
      "def second := 1 /- trailing block", "comment -/", "def third := 2",
      "/-- About the namespace. -/", "namespace Shared", "def fourth := 3",
      'def text := "/-- Not a comment. -/"', "def fifth := 4",
    ].join("\n");
    expect(leanDeclarations(scanLeanSource(source)).map((d) => [d.name.join("."), d.startLine])).toEqual([
      ["first", 2], ["second", 3], ["third", 5], ["Shared.fourth", 8], ["Shared.text", 9], ["Shared.fifth", 10],
    ]);
  });

  it("does not guess short names, private globals, generated fields, or namespace prefixes", () => {
    const target = concept("Lax17.Definitions", "namespace Shared\nprivate def hidden := 0\ndef visible := 1\nstructure Record where\n  field : Nat\nend Shared");
    const caller = concept("Lax17.Caller", [
      "open Shared", "example (visible : Nat) : Nat := visible", "#check Shared.hidden", "#check Shared.Record.field",
      "#check Lax17.Definitions.unknown", "#check Shared.visible", "#check Shared.visible!", "#check Shared.visible?", "#check Shared.visible₁",
    ].join("\n"), [target.id]);
    expect(links(archive([target, caller]), caller.id)).toEqual([{ text: "Shared.visible", href: "../lax-17/Lax17.Definitions.html#L3" }]);
  });

  it("resolves only reachable, unambiguous declarations, even through import cycles", () => {
    const first = concept("Lax17.First", "def Shared.thing := 0", ["Lax17.Second"]);
    const second = concept("Lax17.Second", "", [first.id]);
    const unrelated = concept("Lax17.Other", "def Shared.thing := 1\ndef Unrelated.value := 2");
    const caller = concept("Lax17.Caller", "#check Shared.thing\n#check Unrelated.value\n#check Lax17.Other", [second.id]);
    expect(links(archive([first, second, unrelated, caller]), caller.id)).toEqual([
      { text: "Shared.thing", href: "../lax-17/Lax17.First.html#L1" },
    ]);
    caller.imports.push(unrelated.id);
    expect(links(archive([unrelated, caller, second, first]), caller.id).map((link) => link.text)).toEqual(["Unrelated.value", "Lax17.Other"]);
  });

  it("does not turn local dotted let names or projections through binders into global links", () => {
    const target = concept("Lax17.Target", "def Shared.thing := 0");
    for (const source of [
      "example := let Shared.thing := 1; Shared.thing",
      "example (Shared : Record) := Shared.thing",
      "example := fun Shared => Shared.thing",
      "example := let (Shared, x) := pair; Shared.thing",
    ]) {
      const caller = concept("Lax17.Caller", source, [target.id]);
      expect(links(archive([target, caller]), caller.id)).toEqual([]);
    }
  });

  it("keeps comments, literals and syntax quotations out of the inventory and links", () => {
    const target = concept("Lax17.Target", "def Shared.thing := 0");
    const caller = concept("Lax17.Caller", [
      "-- Shared.thing", "/- outer /- def Fake.nested := Shared.thing -/ Shared.thing -/",
      'def literal := "Shared.thing -- /- \\\" def Fake.string := 0"',
      'def raw := r##" " Shared.thing /- def Fake.raw := 0 "##',
      "def char := 'x'", "def name := `Shared.thing", "def quoted := `(do", "  let x := (Shared.thing)",
      "  pure x)", "def command := `(command|", "def Fake.quoted := Shared.thing)", "#check Shared.thing",
    ].join("\n"), [target.id]);
    const inventory = leanDeclarations(scanLeanSource(caller.sourceText));
    expect(inventory.map((d) => d.name.join("."))).toEqual(["literal", "raw", "char", "name", "quoted", "command"]);
    expect(links(archive([target, caller]), caller.id).filter((link) => link.text === "Shared.thing")).toHaveLength(1);
  });

  it("handles quoted components, Unicode, primes, subscripts and astral UTF-16 offsets", async () => {
    const names = ["α₁", "test!", "test?", "test'", "𝒜", "«with spaces»", "«a.b»", '«<img src=x onerror="boom">»'];
    const target = concept("Lax17.Target", names.map((name) => `def Shared.${name} := 0`).join("\n"));
    const caller = concept("Lax17.Caller", names.map((name) => `#check Shared.${name}`).join("\n") + "\n#check Shared.a.b", [target.id]);
    const model = archive([target, caller]);
    expect(links(model, caller.id).map((link) => link.text)).toEqual(names.map((name) => `Shared.${name}`));
    const html = await highlightSource(caller.sourceText, [], new Set(), { links: sourceLinks(model, caller.id, "../") });
    expect(renderedLinks(html).map((link) => link.text)).toEqual(names.map((name) => `Shared.${name}`));
    expect(html).not.toContain("<img");
    expect(html).toContain("&lt;img");
  });

  it("does not keep stale navigation across builds or mutate cached relative links", () => {
    const target = concept("Lax17.Target", "def Shared.thing := 0");
    const caller = concept("Lax17.Caller", "#check Shared.thing", [target.id]);
    const model = archive([target, caller]);
    const relative = sourceLinks(model, caller.id, "../");
    expect(sourceLinks(model, caller.id, "../../")[0]!.href).toBe("../../lax-17/Lax17.Target.html#L1");
    expect(sourceLinks(model, caller.id, "../")).toEqual(relative);
    target.sourceText = "\n\ndef Shared.thing := 0";
    expect(sourceLinks(archive([target, caller]), caller.id, "../")[0]!.href).toMatch(/#L3$/u);
  });
});

describe("rendered source links", () => {
  it("retains text, source rows, colours, and one anchor per identifier", async () => {
    const source = "#check Shared.thing\r\n#check Shared.thing\r\n";
    const links = [...source.matchAll(/Shared\.thing/gu)].map((match) => ({ start: match.index, end: match.index + match[0].length, href: "../lax-17/Lax17.Target.html#L1" }));
    const html = await highlightSource(source, [], new Set(), { links });
    expect(renderedLinks(html)).toHaveLength(2);
    expect(html.match(/<tr id="L\d+"/gu)).toHaveLength(3);
    const rows = [...html.matchAll(/<td class="line-code">([^]*?)<\/td>/gu)].map((match) => strip(match[1]!));
    expect(rows).toEqual(["#check Shared.thing", "#check Shared.thing", " "]);
    expect(html).toMatch(/class="lean-identifier-link"[^>]*><span style="color:/u);
  });

  it("preserves offsets after inline and multiline comment math without placeholders", async () => {
    const source = "/- $x^2$ -/ #check Shared.thing\n/- $$\n x+y\n$$ -/ #check Shared.thing\n-- LAXSOURCELINKTOKEN0END";
    const target = concept("Lax17.Target", "def Shared.thing := 0");
    const caller = concept("Lax17.Caller", source, [target.id]);
    const html = await highlightSource(source, [], new Set(), { links: sourceLinks(archive([target, caller]), caller.id, "../"), anchors: false });
    expect(renderedLinks(html).map((link) => link.text)).toEqual(["Shared.thing", "Shared.thing"]);
    expect(html.match(/class="katex"/gu)).toHaveLength(2);
    expect(html.match(/<tr /gu)).toHaveLength(5);
    expect(html).not.toMatch(/\bid="[Ls]/u);
    expect(html).toContain("LAXSOURCELINKTOKEN0END");
    expect(html).not.toContain("$x^2$");
  });

  it("refuses active/external hrefs and malformed ranges", async () => {
    const source = "Shared.thing";
    for (const href of ["javascript:alert(1)", "data:text/html,bad", "//evil.test/a", "https://evil.test/a", '../lax-17/x.html" onclick="bad', "../x\\y/x.html"]) {
      expect(renderedLinks(await highlightSource(source, [], new Set(), { links: [{ start: 0, end: source.length, href }] }))).toEqual([]);
    }
    expect(renderedLinks(await highlightSource(source, [], new Set(), {
      links: [{ start: -1, end: Infinity, href: "../lax-17/Lax17.Target.html" }],
    }))).toEqual([]);
  });

  it("renders thousands of references without lost links or placeholder collisions", async () => {
    const source = "#check Shared.thing\n".repeat(3000);
    const target = concept("Lax17.Target", "def Shared.thing := 0");
    const caller = concept("Lax17.Caller", source, [target.id]);
    const html = await highlightSource(source, [], new Set(), { links: sourceLinks(archive([target, caller]), caller.id, "../") });
    expect(renderedLinks(html)).toHaveLength(3000);
    expect(html.match(/<tr id="L\d+"/gu)).toHaveLength(3001);
  });

  it("keeps links and escaping when syntax highlighting is unavailable", async () => {
    vi.resetModules();
    vi.doMock("shiki", () => ({ createHighlighter: () => Promise.reject(new Error("unavailable")) }));
    try {
      const { highlightSource: fallback } = await import("../src/sitegen/highlight.js");
      const html = await fallback("Shared.thing <script>\n-- $x$", [], new Set(), {
        links: [{ start: 0, end: 12, href: "../lax-17/Lax17.Target.html#L1" }],
      });
      expect(renderedLinks(html)).toEqual([{ text: "Shared.thing", href: "../lax-17/Lax17.Target.html#L1" }]);
      expect(html).toContain("&lt;script&gt;");
      expect(html).toContain('class="katex"');
    } finally { vi.doUnmock("shiki"); vi.resetModules(); }
  });
});
