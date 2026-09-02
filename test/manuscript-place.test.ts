import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

// The viewer's pure placement rules, run as the browser runs them: one
// script evaluated in an empty context, exposing `laxManuscript`.
const context: Record<string, unknown> = {};
vm.createContext(context);
vm.runInContext(fs.readFileSync("assets/site/manuscript-place.js", "utf8"), context);

type Item = { x: number; y: number; w: number; h: number; str?: string };
type Point = { page: number; x: number; y: number; mode: "v" | "h" };
type Mark = { begin: Point; end: Point };
type Segment = { page: number; from: number; to: number; clipLeft?: number; clipRight?: number };
type Analysed = { items: Item[]; blocks: { idx: number[] }[]; flow: { first: number; last: number } };
const place = context.laxManuscript as {
  textItems(content: { items: unknown[] }): Item[];
  analyzePage(items: Item[]): Analysed;
  resolveRange(mark: Mark, pages: (Analysed | undefined)[]): {
    begin: { page: number; item: number; clipX: number | null };
    end: { page: number; item: number; clipX: number | null };
    segments: Segment[];
  } | null;
  segmentRects(pd: Analysed, seg: Segment): { x0: number; x1: number; top: number; bot: number }[];
  segmentShapes(pd: Analysed, seg: Segment): { points: [number, number][]; x0: number; x1: number; top: number; bot: number }[];
  stackCards(cards: { want: number; height: number }[], gap: number): number[];
};

// A two-column LaTeX page in content-stream order: column 1 top to bottom,
// column 2 top to bottom, then the folio. Every line is two items (a left
// and a right half) so the horizontal clip rule has something to choose.
const LEADING = 12;
const TOP = 700;
const LINES = 20;
const COLUMNS = [72, 310.6];
const COLUMN_WIDTH = 218;
function twoColumnPage(): { items: Item[]; line(column: number, index: number): number } {
  const items: Item[] = [];
  for (const x of COLUMNS) {
    for (let index = 0; index < LINES; index++) {
      const y = TOP - index * LEADING;
      items.push({ x, y, w: COLUMN_WIDTH / 2, h: 10, str: `c${x}l${index}a` });
      items.push({ x: x + COLUMN_WIDTH / 2, y, w: COLUMN_WIDTH / 2, h: 10, str: `c${x}l${index}b` });
    }
  }
  items.push({ x: 297, y: 50, w: 5, h: 10, str: "1" });
  return { items, line: (column, index) => (column * LINES + index) * 2 };
}
const baseline = (index: number) => TOP - index * LEADING;

describe("paper viewer placement", () => {
  it("reads pdf.js text items and drops marked-content pseudo items", () => {
    const items = place.textItems({ items: [
      { transform: [1, 0, 0, 1, 72, 700], width: 40, height: 10, str: "a" },
      { type: "beginMarkedContent" },
      { transform: [1, 0, 0, 1, 72, 688], width: 40, height: 0, str: "b" },
    ] });
    expect(items).toEqual([{ x: 72, y: 700, w: 40, h: 10, str: "a" }, { x: 72, y: 688, w: 40, h: 10, str: "b" }]);
  });

  it("cuts the content order into column blocks and keeps the folio out of the flow", () => {
    const { items, line } = twoColumnPage();
    const pd = place.analyzePage(items);
    expect(pd.blocks.map((b) => b.idx.length)).toEqual([LINES * 2, LINES * 2, 1]);
    expect(pd.flow).toEqual({ first: 0, last: line(1, LINES - 1) + 1 });
  });

  it("clips an inline begin at x and a vertical begin starts on the next line", () => {
    const { items, line } = twoColumnPage();
    const pages = [place.analyzePage(items)];
    // Inline: the point sits in the right half of line 3 of column 1.
    const inline = place.resolveRange({
      begin: { page: 1, x: 72 + 150, y: baseline(3), mode: "h" },
      end: { page: 1, x: 72 + 200, y: baseline(3), mode: "h" },
    }, pages)!;
    expect(inline.begin).toEqual({ page: 1, item: line(0, 3) + 1, clipX: 222 });
    expect(inline.end).toEqual({ page: 1, item: line(0, 3) + 1, clipX: 272 });
    const rects = place.segmentRects(pages[0]!, inline.segments[0]!);
    expect(rects).toHaveLength(1);
    expect(rects[0]).toMatchObject({ x0: 222, x1: 272 });
    expect(rects[0]!.top).toBeGreaterThan(baseline(3));
    expect(rects[0]!.bot).toBeLessThan(baseline(3));
    // Vertical: pdfTeX reports the baseline of the line *above* the marker,
    // so the same y in v mode begins one line later, at the column's edge.
    const vertical = place.resolveRange({
      begin: { page: 1, x: 72, y: baseline(3), mode: "v" },
      end: { page: 1, x: 72, y: baseline(5), mode: "v" },
    }, pages)!;
    expect(vertical.begin).toEqual({ page: 1, item: line(0, 4), clipX: null });
    expect(vertical.end).toEqual({ page: 1, item: line(0, 5) + 1, clipX: null });
    expect(place.segmentRects(pages[0]!, vertical.segments[0]!)).toHaveLength(2);
  });

  it("starts below a point between baselines and moves to the next column at the foot", () => {
    const { items, line } = twoColumnPage();
    const pages = [place.analyzePage(items)];
    const between = place.resolveRange({
      begin: { page: 1, x: 72, y: baseline(2) - 5, mode: "v" },
      end: { page: 1, x: 72, y: baseline(4) - 5, mode: "v" },
    }, pages)!;
    expect(between.begin.item).toBe(line(0, 3));
    expect(between.end.item).toBe(line(0, 4) + 1);
    // Below the last line of column 1 nothing follows in that block: the
    // passage begins at the top of column 2, not on the folio.
    const foot = place.resolveRange({
      begin: { page: 1, x: 72, y: baseline(LINES - 1) - 8, mode: "v" },
      end: { page: 1, x: 310.6 + 50, y: baseline(1), mode: "h" },
    }, pages)!;
    expect(foot.begin.item).toBe(line(1, 0));
    expect(foot.end).toEqual({ page: 1, item: line(1, 1), clipX: 360.6 });
    // Never compares y across blocks: the same baseline exists in column 2.
    expect(foot.segments).toEqual([{ page: 1, from: line(1, 0), to: line(1, 1), clipLeft: undefined, clipRight: 360.6 }]);
  });

  it("spans pages through the flow and refuses unanalysed pages", () => {
    const first = twoColumnPage();
    const second = twoColumnPage();
    const pages = [place.analyzePage(first.items), place.analyzePage(second.items)];
    const mark: Mark = {
      begin: { page: 1, x: 310.6, y: baseline(LINES - 1), mode: "v" },
      end: { page: 2, x: 72 + 60, y: baseline(2), mode: "h" },
    };
    const spanning = place.resolveRange(mark, pages)!;
    // The last line of column 2 is the *preceding* line, so page 1 has
    // nothing left and the passage begins with page 2's first flow item.
    expect(spanning.begin).toEqual({ page: 2, item: 0, clipX: null });
    expect(spanning.end).toEqual({ page: 2, item: second.line(0, 2), clipX: 132 });
    expect(spanning.segments).toEqual([{ page: 2, from: 0, to: second.line(0, 2), clipLeft: undefined, clipRight: 132 }]);
    expect(place.resolveRange(mark, [pages[0]])).toBeNull();
    const straddling = place.resolveRange({
      begin: { page: 1, x: 310.6 + 20, y: baseline(LINES - 2), mode: "h" },
      end: mark.end,
    }, pages)!;
    expect(straddling.segments.map((s) => s.page)).toEqual([1, 2]);
    expect(straddling.segments[0]!.to).toBe(pages[0]!.flow.last);
    expect(place.segmentRects(pages[0]!, straddling.segments[0]!)).toHaveLength(2);
  });

  it("draws a passage as one region per column, first and last lines clipped", () => {
    const { items, line } = twoColumnPage();
    const pages = [place.analyzePage(items)];
    // mid-line 5 of column 1 to mid-line 2 of column 2
    const range = place.resolveRange({
      begin: { page: 1, x: 150, y: baseline(5), mode: "h" },
      end: { page: 1, x: 400, y: baseline(2), mode: "h" },
    }, pages)!;
    expect(range.segments).toHaveLength(1);
    const shapes = place.segmentShapes(pages[0]!, range.segments[0]!);
    expect(shapes).toHaveLength(2);
    const [left, right] = shapes as [typeof shapes[0], typeof shapes[0]];
    // column 1: starts at the clip, runs to the column's right edge, ends at its foot
    expect(left.points).toHaveLength(8);
    expect(left.points[0]).toEqual([150, baseline(5) + 8.6]);
    expect(left.points[1]![0]).toBeCloseTo(COLUMNS[0]! + COLUMN_WIDTH);
    expect(left.points[5]![0]).toBeCloseTo(COLUMNS[0]!);
    expect(left.bot).toBeCloseTo(baseline(LINES - 1) - 2.2);
    // the leading between lines is filled: the cut after line 5 lies between its box and line 6's
    expect(left.points[7]![1]).toBeCloseTo((baseline(5) - 2.2 + baseline(6) + 8.6) / 2);
    // column 2: from its left edge, ending at the clip on line 2
    expect(right.points[0]).toEqual([COLUMNS[1], baseline(0) + 8.6]);
    expect(right.points[4]![0]).toBe(400);
    expect(right.x0).toBeCloseTo(COLUMNS[1]!);
    expect(range.segments[0]!.from).toBe(line(0, 5)); // the first half of line 5 passes x=150
    // a single line is a plain rectangle
    const one = place.resolveRange({
      begin: { page: 1, x: 80, y: baseline(3), mode: "h" },
      end: { page: 1, x: 250, y: baseline(3), mode: "h" },
    }, pages)!;
    expect(place.segmentShapes(pages[0]!, one.segments[0]!)).toEqual([
      { points: [[80, baseline(3) + 8.6], [250, baseline(3) + 8.6], [250, baseline(3) - 2.2], [80, baseline(3) - 2.2]], x0: 80, x1: 250, top: baseline(3) + 8.6, bot: baseline(3) - 2.2 },
    ]);
  });

  it("keeps a display formula's raised delimiters on its line and out of a new run", () => {
    const items: Item[] = [
      { x: 72, y: 600, w: 200, h: 10, str: "We set" },
      { x: 207, y: 574, w: 28, h: 10, str: "f(t) =" },
      { x: 238, y: 585, w: 5, h: 10, str: "⌈" }, // pdfTeX places the tall bracket on a raised baseline
      { x: 243, y: 574, w: 100, h: 10, str: "2 + C" },
      { x: 275, y: 578, w: 40, h: 7, str: "(1−ε)t" },
      { x: 366, y: 585, w: 5, h: 10, str: "⌉" },
      { x: 72, y: 548, w: 200, h: 10, str: "where" },
    ];
    const pd = place.analyzePage(items);
    const seg = { page: 1, from: 0, to: items.length - 1 };
    const rects = place.segmentRects(pd, seg);
    expect(rects).toHaveLength(3);
    expect(rects[1]).toMatchObject({ x0: 207, x1: 371, top: 585 + 8.6, bot: 574 - 2.2 });
    expect(place.segmentShapes(pd, seg)).toHaveLength(1);
  });

  it("merges a display formula's fractions into their rows and the rows into one region", () => {
    // pdfTeX's content order for two rows of an aligned display (page 9 of
    // lax-48's paper): numerators and denominators come with their row,
    // each dropping or rising against the row's baseline, and the second
    // row starts a new block by the drop.
    const items: Item[] = [
      { x: 72, y: 620, w: 300, h: 10, str: "This is a contradiction since" },
      { x: 167.2, y: 598.3, w: 7.7, h: 10, str: "⩾" },
      { x: 186.3, y: 591.5, w: 8.9, h: 10, str: "(1" },
      { x: 222.3, y: 598.3, w: 12.7, h: 10, str: "log" },
      { x: 131.3, y: 566.7, w: 7.7, h: 10, str: "=" },
      { x: 141.8, y: 577.8, w: 5.9, h: 10, str: "(" },
      { x: 147.8, y: 566.7, w: 18.8, h: 10, str: "(2 +" },
      { x: 275.6, y: 559.9, w: 2.8, h: 10, str: "|" },
      { x: 72, y: 530, w: 300, h: 10, str: "since, we recall," },
    ];
    const pd = place.analyzePage(items);
    expect(pd.blocks.length).toBeGreaterThan(1);
    const seg = { page: 1, from: 0, to: items.length - 1 };
    const rects = place.segmentRects(pd, seg);
    expect(rects).toHaveLength(4);
    expect(rects[1]).toMatchObject({ x0: 167.2, top: 598.3 + 8.6, bot: 591.5 - 2.2 });
    expect(rects[2]).toMatchObject({ x0: 131.3, top: 577.8 + 8.6, bot: 559.9 - 2.2 });
    const shapes = place.segmentShapes(pd, seg);
    expect(shapes).toHaveLength(1);
    expect(shapes[0]!.points).toHaveLength(8);
    expect(shapes[0]!.top).toBeCloseTo(628.6);
    expect(shapes[0]!.bot).toBeCloseTo(527.8);
  });

  it("keeps a running head out of the flow like the folio", () => {
    const { items } = twoColumnPage();
    const withHead: Item[] = [
      { x: 72, y: 760, w: 80, h: 10, str: "É. Bonnet, H. Déprés" },
      { x: 520, y: 760, w: 6, h: 10, str: "5" },
      ...items,
    ];
    const pd = place.analyzePage(withHead);
    expect(pd.flow.first).toBe(2);
    expect(pd.flow.last).toBe(withHead.length - 2);
    // a section heading close above its paragraph stays in the flow
    const withHeading: Item[] = [{ x: 72, y: TOP + 22, w: 120, h: 12, str: "3 Proof of Theorem 4" }, ...items];
    expect(place.analyzePage(withHeading).flow.first).toBe(0);
  });

  it("stacks cards greedily in the given order", () => {
    expect(place.stackCards([
      { want: 100, height: 40 },
      { want: 110, height: 40 },
      { want: 400, height: 20 },
      { want: 50, height: 30 },
    ], 8)).toEqual([100, 148, 400, 428]);
  });
});
