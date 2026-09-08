import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";
import protobuf from "protobufjs";
import { extractBundleTar } from "../src/bundles.js";
import { FIXTURE_TAR } from "./paper-web-archive.js";

// The vendored viewer decodes blocks with its own fixed-schema proto2 wire
// decoder (protobuf.js's reflection decoder is built by runtime code
// generation, which the site CSP forbids — viewer modification 5). This
// proves the replacement equivalent: over the committed fixture block —
// glyphs, glue, kerns (negative ints), doubles, nested boxes, a picture,
// markers at every capture site — the decoder's output deep-equals what
// protobuf.js toObject({defaults:false, arrays:true, enums:String,
// longs:Number}) produces from the bundle's own schema.

function viewerContext(): Record<string, any> {
  const noop = () => {};
  const stub = { addEventListener: noop, removeEventListener: noop };
  const context: Record<string, any> = {
    console: { log: noop, error: noop, warn: noop },
    window: { ...stub },
    document: { ...stub, currentScript: null, getElementById: () => null, createElement: () => { throw new Error("no DOM in this test"); }, fonts: undefined, documentElement: { setAttribute: noop } },
    ResizeObserver: class { observe() {} unobserve() {} },
    IntersectionObserver: class { observe() {} unobserve() {} },
    CustomEvent: class {},
    TextDecoder,
    performance: { now: () => 0 },
    requestAnimationFrame: noop,
    atob: (b64: string) => Buffer.from(b64, "base64").toString("latin1"),
  };
  context.window.document = context.document;
  vm.createContext(context);
  vm.runInContext(fs.readFileSync("assets/site/reflowtex/latex-viewer.js", "utf8"), context);
  return context;
}

describe("the viewer's fixed-schema decoder", () => {
  const files = extractBundleTar(fs.readFileSync(FIXTURE_TAR));
  const block = files.get("blocks/000.pb")!;
  const schemaText = files.get("schema/latex.proto")!.toString("utf8");

  it("deep-equals protobuf.js over the committed fixture block", () => {
    const docType = protobuf.parse(schemaText, { keepCase: true }).root.lookupType("latex.Document");
    const reference = docType.toObject(docType.decode(block), { defaults: false, arrays: true, enums: String, longs: Number });
    const decoded = viewerContext().window.laxLatexViewer.decodeBlock(new Uint8Array(block));
    expect(JSON.parse(JSON.stringify(decoded))).toEqual(JSON.parse(JSON.stringify(reference)));
    // And the content the page depends on is really in there.
    expect(decoded.paragraphs.length).toBeGreaterThan(0);
    expect(decoded.content.some((item: { kind: string }) => item.kind === "marker")).toBe(true);
    expect(decoded.content.some((item: { kind: string }) => item.kind === "display")).toBe(true);
    expect(decoded.pictures).toHaveLength(1);
    const marks: Array<{ side: string; n: number }> = [];
    const walk = (nodes: any[]) => {
      for (const node of nodes) {
        if (node.type === "mark") marks.push({ side: node.side, n: node.n });
        for (const key of ["children", "replace", "pre", "post"]) if (node[key]) walk(node[key]);
      }
    };
    for (const paragraph of decoded.paragraphs) walk(paragraph.nodes);
    expect(marks).toContainEqual({ side: "b", n: 1 });
    expect(marks).toContainEqual({ side: "e", n: 1 });
    // Negative int32 fields survive the ten-byte varint form.
    const kerns: number[] = [];
    const walkKerns = (nodes: any[]) => {
      for (const node of nodes) {
        if (node.type === "kern" && typeof node.kern === "number") kerns.push(node.kern);
        for (const key of ["children", "replace", "pre", "post"]) if (node[key]) walkKerns(node[key]);
      }
    };
    for (const paragraph of decoded.paragraphs) walkKerns(paragraph.nodes);
    expect(kerns.some((kern) => kern < 0)).toBe(true);
  });

  // The band width the schema gained as Paragraph field 7 (the \parshape
  // width the serializer has always recorded beside `indent`, and the only
  // statement of a paragraph's right inset — see paraBand). The committed
  // fixture predates the field, so the round trip is proved over a small
  // document encoded by the fork's own descriptor-driven encoder against the
  // new schema:
  //
  //   PYTHONPATH=<checkout>/build python -c "import encode_pb; \\
  //     encode_pb.serialize_document({...two paragraphs, one inset...})"
  //
  // Paragraph 1 is a body paragraph ({0, hsize}); paragraph 2 is inset on
  // both sides ({indent, hsize - indent - right}), the case the field exists
  // for. Recut this constant only if the encoder's shape changes.
  const WIDTH_BLOCK_B64 =
    "CjAIARIRbG1yb21hbjEwLXJlZ3VsYXIYgIAoIhVsbXJvbWFuMTAtcmVndWxhci5vdGYSHAoJCAAQQRgB" +
    "gAIBEAAYgIAwIICABCgAOICAoAsSJgoJCAAQQhgBgAIBEP+/bRiAgDAggIAEKAAyBmNlbnRlcjiCgMUJ" +
    "GgQIABABGgQIABACKgoIgKgdEKrjGxgA";

  it("reads the paragraph band width the new schema carries", () => {
    const decoded = viewerContext().window.laxLatexViewer.decodeBlock(new Uint8Array(Buffer.from(WIDTH_BLOCK_B64, "base64")));
    const bands = decoded.paragraphs.map((paragraph: { indent?: number; width?: number }) => [paragraph.indent, paragraph.width]);
    expect(bands).toEqual([[0, 23592960], [1794047, 20004866]]);
    // The rest of the paragraph is untouched by the new field.
    expect(decoded.paragraphs[1].align).toBe("center");
    expect(decoded.paragraphs[1].baselineskip).toBe(786432);
    expect(decoded.paragraphs[1].nodes[0]).toMatchObject({ type: "glyph", char: 66, font: 1, metrics: 1 });
    // hsize is the widest band; the inset paragraph's right inset follows.
    const hsize = Math.max(...decoded.paragraphs.map((paragraph: { width: number }) => paragraph.width));
    expect(hsize - (decoded.paragraphs[1].indent ?? 0) - decoded.paragraphs[1].width).toBe(1794047);
  });

  it("leaves width absent for a bundle sealed before the field existed", () => {
    // Old bundles must keep rendering: the fixture's paragraphs carry no
    // field 7, and the decoder reports it as absent rather than 0.
    const decoded = viewerContext().window.laxLatexViewer.decodeBlock(new Uint8Array(block));
    expect(decoded.paragraphs.every((paragraph: { width?: number }) => paragraph.width === undefined)).toBe(true);
  });

  it("fails closed on truncated and malformed bytes", () => {
    const decodeBlock = viewerContext().window.laxLatexViewer.decodeBlock;
    // Cutting into the final field leaves a length prefix overrunning the
    // buffer (a cut at byte 50 can land between fields and decode cleanly —
    // prefix framing makes that legal, which is why the digest is verified
    // upstream of decoding).
    expect(() => decodeBlock(new Uint8Array(block.subarray(0, block.length - 3)))).toThrow(/truncated/);
    expect(() => decodeBlock(new Uint8Array([0x0b]))).toThrow(/wire type/);
    expect(() => decodeBlock(new Uint8Array([0x80, 0x80, 0x80]))).toThrow(/truncated varint/);
  });
});
