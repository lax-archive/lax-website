// Pure placement for the paper viewer: from a page's text items (pdf.js
// getTextContent, in content-stream order) and a mark's two destination
// points, to the text items the passage covers and one rectangle per line.
// Everything is in PDF user space (points, origin bottom-left); manuscript.js
// converts to pixels. No DOM here, so the rules are testable in node:vm.
//
// The boundary rule (spike/paper/viewer/REPORT.md in the lax repository):
// content-stream order is reading order for a LaTeX page — column 1 top to
// bottom, then column 2, then the folio — so items are never re-sorted, only
// cut into *blocks* where the baseline jumps: up by more than COL_JUMP (a
// new column) or down by more than GAP_SPLIT (a heading, the folio). For a
// begin point (page, x, y) in TeX mode m:
//   0. take the block whose box contains the point, else the nearest; never
//      compare y across blocks (two columns share every baseline);
//   1. S = the block's items with baseline within Y_TOL of y;
//   2. m = h (inside a line): the first item of S whose right edge passes x,
//      its rectangle clipped at x; nothing past x → the first item after S;
//   3. m = v (between blocks): S is the *preceding* line — pdfTeX reports the
//      baseline of the last line typeset — so start after S;
//   4. S empty: the first item of the block below y; none → the first item
//      of the next block (a marker at the foot of column 1 lands in column 2);
//   5. nothing left on the page: the first flow item of the next page.
// End points mirror this with last for first and the clip on the right.
(() => {
  const Y_TOL = 3;      // pt: baselines this close are one line (subscripts stay; leading is ~12)
  const COL_JUMP = 20;  // pt: a baseline rising this much starts a block (new column)
  const GAP_SPLIT = 22; // pt: a baseline dropping this much starts a block (heading, folio)

  // pdf.js text items → {x, y, w, h}; marked-content pseudo items have no transform.
  function textItems(content) {
    const out = [];
    for (const it of content.items) {
      if (!it.transform) continue;
      out.push({ x: it.transform[4], y: it.transform[5], w: it.width, h: it.height || 10, str: it.str });
    }
    return out;
  }

  function computeBlocks(items) {
    const blocks = [];
    let cur = null;
    items.forEach((it, i) => {
      if (cur && (it.y > cur.minY + COL_JUMP || it.y < cur.lastY - GAP_SPLIT)) {
        blocks.push(cur);
        cur = null;
      }
      if (!cur) cur = { idx: [], minY: it.y, maxY: it.y, x0: Infinity, x1: -Infinity, lastY: it.y };
      cur.idx.push(i);
      cur.minY = Math.min(cur.minY, it.y);
      cur.maxY = Math.max(cur.maxY, it.y);
      cur.lastY = it.y;
      if (it.w > 0) {
        cur.x0 = Math.min(cur.x0, it.x);
        cur.x1 = Math.max(cur.x1, it.x + it.w);
      }
    });
    if (cur) blocks.push(cur);
    return blocks;
  }

  // The folio and a running foot are last in content order but not part of
  // the flow: a passage running to the end of a page must not swallow them.
  function flowSpan(blocks) {
    if (!blocks.length) return { first: 0, last: -1 };
    let last = blocks.length - 1;
    while (last > 0) {
      const b = blocks[last];
      const prev = blocks[last - 1];
      if (b.idx.length <= 3 && b.maxY < prev.minY - 15) last--;
      else break;
    }
    return { first: blocks[0].idx[0], last: blocks[last].idx[blocks[last].idx.length - 1] };
  }

  function analyzePage(items) {
    const blocks = computeBlocks(items);
    return { items, blocks, flow: flowSpan(blocks) };
  }

  function findBlock(blocks, x, y) {
    let best = null;
    let bestD = Infinity;
    for (const b of blocks) {
      const dx = Math.max(b.x0 - x, x - b.x1, 0);
      const dy = Math.max(b.minY - y, y - b.maxY, 0);
      const d = Math.hypot(dx, dy);
      if (d < bestD - 1e-6) {
        bestD = d;
        best = b;
      }
    }
    return best;
  }

  function sameLine(pd, blk, y) {
    return blk.idx.filter((i) => Math.abs(pd.items[i].y - y) <= Y_TOL);
  }

  function resolveBegin(pd, point) {
    if (!pd.blocks.length) return { overflow: true };
    const blk = findBlock(pd.blocks, point.x, point.y);
    const S = sameLine(pd, blk, point.y);
    if (S.length) {
      if (point.mode === "h") {
        for (const i of S) {
          const it = pd.items[i];
          if (it.x + it.w > point.x + 0.1) return { index: i, clipX: point.x };
        }
      }
      const after = S[S.length - 1] + 1;
      return after <= pd.flow.last ? { index: after } : { overflow: true };
    }
    for (const i of blk.idx) if (pd.items[i].y < point.y - Y_TOL) return { index: i };
    const next = pd.blocks[pd.blocks.indexOf(blk) + 1];
    if (next && next.idx[0] <= pd.flow.last) return { index: next.idx[0] };
    return { overflow: true };
  }

  function resolveEnd(pd, point) {
    if (!pd.blocks.length) return { underflow: true };
    const blk = findBlock(pd.blocks, point.x, point.y);
    const S = sameLine(pd, blk, point.y);
    if (S.length) {
      if (point.mode === "h") {
        for (let k = S.length - 1; k >= 0; k--) {
          const it = pd.items[S[k]];
          if (it.x < point.x - 0.1) return { index: S[k], clipX: point.x };
        }
        const before = S[0] - 1;
        return before >= pd.flow.first ? { index: before } : { underflow: true };
      }
      return { index: S[S.length - 1] };
    }
    let last = -1;
    for (const i of blk.idx) if (pd.items[i].y > point.y + Y_TOL) last = i;
    if (last >= 0) return { index: last };
    const prev = pd.blocks[pd.blocks.indexOf(blk) - 1];
    if (prev) return { index: prev.idx[prev.idx.length - 1] };
    return { underflow: true };
  }

  // `pages` is indexed by page number minus one; a page not yet analysed
  // (undefined) ends the search, so callers analyse every page a mark spans.
  function resolveRange(mark, pages) {
    const pb = pages[mark.begin.page - 1];
    const pe = pages[mark.end.page - 1];
    if (!pb || !pe) return null;

    let begin = resolveBegin(pb, mark.begin);
    let bPage = mark.begin.page;
    while (begin.overflow) {
      const nxt = pages[bPage];
      if (!nxt) return null;
      bPage += 1;
      if (nxt.flow.last < nxt.flow.first) { begin = { overflow: true }; continue; }
      begin = { index: nxt.flow.first };
    }

    let end = resolveEnd(pe, mark.end);
    let ePage = mark.end.page;
    while (end.underflow) {
      const prv = pages[ePage - 2];
      if (!prv) return null;
      ePage -= 1;
      if (prv.flow.last < prv.flow.first) { end = { underflow: true }; continue; }
      end = { index: prv.flow.last };
    }
    if (ePage < bPage || (ePage === bPage && end.index < begin.index)) return null;

    const segments = [];
    for (let p = bPage; p <= ePage; p++) {
      const pd = pages[p - 1];
      const from = p === bPage ? begin.index : pd.flow.first;
      const to = p === ePage ? end.index : pd.flow.last;
      if (to < from) continue;
      segments.push({
        page: p,
        from,
        to,
        clipLeft: p === bPage ? begin.clipX : undefined,
        clipRight: p === ePage ? end.clipX : undefined,
      });
    }
    if (!segments.length) return null;
    return {
      begin: { page: bPage, item: begin.index, clipX: begin.clipX ?? null },
      end: { page: ePage, item: end.index, clipX: end.clipX ?? null },
      segments,
    };
  }

  // One rectangle per line of a segment: items sharing a baseline merge.
  // {x0, x1, top, bot} in PDF space, top > bot.
  function segmentRects(pd, seg) {
    const lines = [];
    let cur = null;
    for (let i = seg.from; i <= seg.to; i++) {
      const it = pd.items[i];
      if (!it || it.w <= 0) continue;
      let x0 = it.x;
      let x1 = it.x + it.w;
      if (i === seg.from && seg.clipLeft !== undefined) x0 = Math.max(x0, seg.clipLeft);
      if (i === seg.to && seg.clipRight !== undefined) x1 = Math.min(x1, seg.clipRight);
      if (x1 <= x0) continue;
      const h = it.h;
      if (cur && Math.abs(cur.y - it.y) <= Y_TOL && x0 >= cur.x0 - 60) {
        cur.x0 = Math.min(cur.x0, x0);
        cur.x1 = Math.max(cur.x1, x1);
        cur.top = Math.max(cur.top, it.y + h * 0.86);
        cur.bot = Math.min(cur.bot, it.y - h * 0.22);
      } else {
        cur = { y: it.y, x0, x1, top: it.y + h * 0.86, bot: it.y - h * 0.22 };
        lines.push(cur);
      }
    }
    return lines.map(({ x0, x1, top, bot }) => ({ x0, x1, top, bot }));
  }

  // The rail: every card wants the y of its passage; in the given order a
  // card that would overlap the one before is pushed down by `gap`.
  function stackCards(cards, gap) {
    let cursor = -Infinity;
    return cards.map((card) => {
      const top = Math.max(card.want, cursor + gap);
      cursor = top + card.height;
      return top;
    });
  }

  const api = { textItems, analyzePage, computeBlocks, flowSpan, resolveRange, segmentRects, stackCards };
  if (typeof window !== "undefined") window.laxManuscript = api;
  else if (typeof globalThis !== "undefined") globalThis.laxManuscript = api;
})();
