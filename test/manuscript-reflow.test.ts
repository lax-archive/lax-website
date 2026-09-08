import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

// The reflow surface's pure anchor-join math, run as the browser runs it:
// one script in an empty context (no `document`), exposing `laxReflowPlace`
// — the manuscript-place.js testing precedent.
const context: Record<string, unknown> = {};
vm.createContext(context);
vm.runInContext(fs.readFileSync("assets/site/manuscript-reflow.js", "utf8"), context);

type Key = number | string;
type Anchor = { n: Key; side: "b" | "e"; top: number; bottom?: number; x?: number; inline?: boolean };
type Band = { top: number; bottom: number; begin?: Anchor; end?: Anchor };
const place = context.laxReflowPlace as {
  bands(anchors: Anchor[]): Record<Key, Band>;
  place(
    cards: { n: Key; height: number }[],
    bands: Record<Key, Band>,
    gap: number,
    offset: number,
  ): { tops: number[]; placed: boolean[] };
  railOrder(cards: { n: Key }[], bands: Record<Key, Band>): number[];
  outline(band: Band, width: number): [number, number][];
  contains(points: [number, number][], x: number, y: number): boolean;
};

/** The band's own extent; the anchors it kept are the outline's business. */
const span = (band: Band) => ({ top: band.top, bottom: band.bottom });

describe("reflow card placement", () => {
  it("pairs begin and end anchors into bands, nesting and all", () => {
    // The fixture's shape: m1 inline in one paragraph, m3 nested inside m2,
    // m4 beginning in the stream and ending inside a later paragraph.
    const bands = place.bands([
      { n: 1, side: "b", top: 100 }, { n: 1, side: "e", top: 100 },
      { n: 2, side: "b", top: 220 },
      { n: 3, side: "b", top: 260 }, { n: 3, side: "e", top: 320 },
      { n: 2, side: "e", top: 380 },
      { n: 4, side: "b", top: 500 }, { n: 4, side: "e", top: 640, bottom: 640 },
    ]);
    expect(span(bands[1])).toEqual({ top: 100, bottom: 100 });
    expect(span(bands[2])).toEqual({ top: 220, bottom: 380 });
    expect(span(bands[3])).toEqual({ top: 260, bottom: 320 });
    expect(span(bands[4])).toEqual({ top: 500, bottom: 640 });
  });

  it("collapses missing sides, never inverts a band, and drops junk", () => {
    const bands = place.bands([
      { n: 1, side: "b", top: 50 },
      { n: 2, side: "e", top: 80 },
      { n: 3, side: "e", top: 10 }, { n: 3, side: "b", top: 40 },
      { n: Number.NaN, side: "b", top: 1 },
      { n: 5, side: "b", top: Number.NaN },
    ]);
    expect(span(bands[1])).toEqual({ top: 50, bottom: 50 });      // no end: collapses
    expect(span(bands[2])).toEqual({ top: 80, bottom: 80 });      // no begin: collapses
    expect(span(bands[3])).toEqual({ top: 40, bottom: 40 });      // inverted: clamped
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

  it("stacks by the bands' order, not the marks', an unbanded mark following its predecessor", () => {
    // Mark 3 is marked first but its passage comes last; mark 4 has no
    // anchors and queues after mark 1, the card before it in rail order.
    const bands = { 1: { top: 100, bottom: 120 }, 2: { top: 110, bottom: 130 }, 3: { top: 700, bottom: 720 } };
    const { tops, placed } = place.place(
      [{ n: 3, height: 60 }, { n: 1, height: 40 }, { n: 4, height: 40 }, { n: 2, height: 40 }],
      bands, 8, 0,
    );
    expect(placed).toEqual([true, true, false, true]);
    expect(tops).toEqual([700, 100, 148, 196]);
  });
});

describe("footnote cards among the mark cards", () => {
  // A footnote's reference is one begin-side anchor keyed `fn:<k>`, its
  // line's top and bottom as measureAnchors reports them; with no end side
  // it bands to the point at its line's top (the begin-only rule), which is
  // where its sidenote wants to be, and stacks with the marks by position,
  // not by kind or key.
  it("bands a footnote reference like a begin anchor under its string key", () => {
    const bands = place.bands([
      { n: 1, side: "b", top: 100, bottom: 120, x: 40, inline: true },
      { n: "fn:1", side: "b", top: 240, bottom: 260, x: 300, inline: true },
      { n: 1, side: "e", top: 300, bottom: 320, x: 80, inline: true },
      { n: "fn:2", side: "b", top: 30, bottom: 30, inline: false },   // a \thanks, in the stream
      { n: "", side: "b", top: 1 },                                    // an empty key is junk
    ]);
    expect(span(bands[1])).toEqual({ top: 100, bottom: 320 });
    expect(span(bands["fn:1"])).toEqual({ top: 240, bottom: 240 });
    expect(bands["fn:1"].begin).toMatchObject({ x: 300, bottom: 260 });
    expect(span(bands["fn:2"])).toEqual({ top: 30, bottom: 30 });
    expect(Object.keys(bands).sort()).toEqual(["1", "fn:1", "fn:2"]);
  });

  it("stacks sidenotes and mark cards together by position, pushing whichever comes later", () => {
    // Mark 1's passage spans a footnote reference; the sidenote wants the
    // reference's line but the mark's card, wanting the passage's top and
    // tall, is in the way, so the sidenote goes below it. Mark 2's passage
    // is below that; footnote 2 sits far down alone.
    const bands = {
      1: { top: 100, bottom: 320 }, "fn:1": { top: 240, bottom: 260 },
      2: { top: 400, bottom: 420 }, "fn:2": { top: 900, bottom: 920 },
    };
    const { tops, placed } = place.place(
      [{ n: 1, height: 200 }, { n: 2, height: 40 }, { n: "fn:1", height: 60 }, { n: "fn:2", height: 30 }],
      bands, 8, 0,
    );
    expect(placed).toEqual([true, true, true, true]);
    expect(tops).toEqual([100, 400, 308, 900]);   // fn:1 at 100+200+8; mark 2 clears it and lands on its passage
  });

  it("orders the rail by position, a card without a band following its predecessor", () => {
    const bands = { 1: { top: 500, bottom: 520 }, "fn:1": { top: 120, bottom: 140 }, 2: { top: 120, bottom: 300 } };
    // Rail order as it stands: the marks first (the record's order), the
    // footnote cards appended as the viewer revealed them, mark 3 unlocated.
    const order = place.railOrder([{ n: 1 }, { n: 2 }, { n: 3 }, { n: "fn:1" }], bands);
    // Mark 2 and the sidenote want the same line: mark 2 keeps its earlier
    // rail place; mark 3 follows mark 2 (its predecessor) and so comes
    // before the sidenote only by that tie rule — then mark 1, last.
    expect(order).toEqual([1, 2, 3, 0]);
    // The same cards already in position order stay put.
    expect(place.railOrder([{ n: 2 }, { n: "fn:1" }, { n: 1 }], bands)).toEqual([0, 1, 2]);
  });

  it("lets an unlocated sidenote queue after the card before it", () => {
    const bands = { 1: { top: 100, bottom: 120 }, 2: { top: 600, bottom: 620 } };
    const { tops, placed } = place.place(
      [{ n: 1, height: 50 }, { n: "fn:1", height: 40 }, { n: 2, height: 50 }],
      bands, 8, 0,
    );
    expect(placed).toEqual([true, false, true]);
    expect(tops).toEqual([100, 158, 600]);
  });
});

describe("the passage outline", () => {
  // The anchors as measureAnchors reports them: a line's top and bottom, an
  // x, and whether the anchor sits in a paragraph (pinned) or in the stream.
  const at = (n: number, side: "b" | "e", top: number, bottom: number, x: number, inline = true) =>
    ({ n, side, top, bottom, x, inline });

  it("runs from the begin anchor to the line end, full lines, then to the end anchor", () => {
    const band = place.bands([at(1, "b", 100, 120, 300), at(1, "e", 180, 200, 250)])[1];
    expect(place.outline(band, 800)).toEqual([
      [300, 100], [800, 100],   // the begin line, from the anchor to the right edge
      [800, 180], [250, 180],   // down the right edge to the end anchor's line
      [250, 200], [0, 200],     // the end line, back to the left edge
      [0, 120], [300, 120],     // up the left edge to the begin anchor's line
    ]);
  });

  it("is one box where the passage begins and ends on the same line", () => {
    const band = place.bands([at(2, "b", 100, 120, 200), at(2, "e", 100, 120, 500)])[2];
    expect(place.outline(band, 800)).toEqual([[200, 100], [500, 100], [500, 120], [200, 120]]);
  });

  it("spans the column for anchors that sit in the stream", () => {
    const band = place.bands([at(3, "b", 40, 40, 0, false), at(3, "e", 300, 300, 0, false)])[3];
    expect(place.outline(band, 800)).toEqual([[0, 40], [800, 40], [800, 300], [0, 300]]);
  });

  it("hit-tests a passage's polygon", () => {
    const band = place.bands([at(4, "b", 100, 120, 300), at(4, "e", 180, 200, 250)])[4];
    const points = place.outline(band, 800);
    expect(place.contains(points, 400, 110)).toBe(true);   // on the begin line, right of the anchor
    expect(place.contains(points, 100, 110)).toBe(false);  // on the begin line, before it starts
    expect(place.contains(points, 100, 150)).toBe(true);   // a full line between
    expect(place.contains(points, 400, 190)).toBe(false);  // on the end line, past the anchor
    expect(place.contains(points, 100, 190)).toBe(true);   // on the end line, before it
  });
});
