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

  it("stacks cards greedily in the given order", () => {
    expect(place.stackCards([
      { want: 100, height: 40 },
      { want: 110, height: 40 },
      { want: 400, height: 20 },
      { want: 50, height: 30 },
    ], 8)).toEqual([100, 148, 400, 428]);
  });
});
