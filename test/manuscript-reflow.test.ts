import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

// The reflow surface's pure anchor-join math, run as the browser runs it:
// one script in an empty context (no `document`), exposing `laxReflowPlace`
// — the manuscript-place.js testing precedent.
const context: Record<string, unknown> = {};
vm.createContext(context);
vm.runInContext(fs.readFileSync("assets/site/manuscript-reflow.js", "utf8"), context);

type Anchor = { n: number; side: "b" | "e"; top: number };
const place = context.laxReflowPlace as {
  bands(anchors: Anchor[]): Record<number, { top: number; bottom: number }>;
  place(
    cards: { n: number; height: number }[],
    bands: Record<number, { top: number; bottom: number }>,
    gap: number,
    offset: number,
  ): { tops: number[]; placed: boolean[] };
};

describe("reflow card placement", () => {
  it("pairs begin and end anchors into bands, nesting and all", () => {
    // The fixture's shape: m1 inline in one paragraph, m3 nested inside m2,
    // m4 beginning in the stream and ending inside a later paragraph.
    const bands = place.bands([
      { n: 1, side: "b", top: 100 }, { n: 1, side: "e", top: 100 },
      { n: 2, side: "b", top: 220 },
      { n: 3, side: "b", top: 260 }, { n: 3, side: "e", top: 320 },
      { n: 2, side: "e", top: 380 },
      { n: 4, side: "b", top: 500 }, { n: 4, side: "e", top: 640 },
    ]);
    expect(bands[1]).toEqual({ top: 100, bottom: 100 });
    expect(bands[2]).toEqual({ top: 220, bottom: 380 });
    expect(bands[3]).toEqual({ top: 260, bottom: 320 });
    expect(bands[4]).toEqual({ top: 500, bottom: 640 });
  });

  it("collapses missing sides, never inverts a band, and drops junk", () => {
    const bands = place.bands([
      { n: 1, side: "b", top: 50 },
      { n: 2, side: "e", top: 80 },
      { n: 3, side: "e", top: 10 }, { n: 3, side: "b", top: 40 },
      { n: Number.NaN, side: "b", top: 1 },
      { n: 5, side: "b", top: Number.NaN },
    ]);
    expect(bands[1]).toEqual({ top: 50, bottom: 50 });      // no end: collapses
    expect(bands[2]).toEqual({ top: 80, bottom: 80 });      // no begin: collapses
    expect(bands[3]).toEqual({ top: 40, bottom: 40 });      // inverted: clamped
    expect(Object.keys(bands).map(Number).sort()).toEqual([1, 2, 3]);
  });

  it("stacks cards at their bands, pushing overlaps down by the gap", () => {
    const bands = { 1: { top: 100, bottom: 120 }, 2: { top: 130, bottom: 190 }, 3: { top: 700, bottom: 720 } };
    const { tops, placed } = place.place(
      [{ n: 1, height: 80 }, { n: 2, height: 40 }, { n: 3, height: 60 }],
      bands, 8, 0,
    );
    expect(placed).toEqual([true, true, true]);
    expect(tops[0]).toBe(100);
    expect(tops[1]).toBe(188); // 100 + 80 + 8: pushed below the first card
    expect(tops[2]).toBe(700); // far band: lands exactly at its passage
  });

  it("subtracts the rail offset, clamps to the rail top, and follows through for unbanded marks", () => {
    const bands = { 1: { top: 30, bottom: 40 }, 3: { top: 400, bottom: 420 } };
    const { tops, placed } = place.place(
      [{ n: 1, height: 50 }, { n: 2, height: 50 }, { n: 3, height: 50 }],
      bands, 8, 60,
    );
    // Band top 30 minus offset 60 clamps to the rail's own top.
    expect(tops[0]).toBe(0);
    // Mark 2 has no anchors: it queues after its predecessor, flagged unplaced.
    expect(placed).toEqual([true, false, true]);
    expect(tops[1]).toBe(58);
    expect(tops[2]).toBe(340); // 400 - 60: back on its passage
  });
});
