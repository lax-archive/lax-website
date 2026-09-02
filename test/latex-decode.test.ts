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
