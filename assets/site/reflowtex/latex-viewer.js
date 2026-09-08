// SPDX-License-Identifier: AGPL-3.0-or-later
// latex-viewer.js — the ReflowTeX browser viewer, vendored for the Lax
// archive. Deliberately unminified: serving this source beside the pages
// that run it is how the site meets AGPL §13 (LICENSE.txt in this
// directory).
//
// Upstream: https://github.com/radek-p/reflowtex, src/viewer/latex-viewer.js
// at rev 36f8365eed25ece1db38e0059bcbba3c250802e1. Lax modifications, all
// marked with "lax:" comments; everything else is verbatim upstream:
//   1. Marker anchors. The lax schema extension carries \laxmark positions
//      as `mark` nodes (inside paragraphs) and `marker` content items
//      (between flow items). Both become zero-size anchor elements in the
//      block — id="m<n>" on the begin side, data-mark/data-side on both
//      sides — placed at layout time from the renderer's own walk and
//      re-anchored on every reflow, resize, and font repaint. A stream
//      marker closes the current text segment so its anchor can sit in
//      flow between the segments (the inter-segment margin reproduces the
//      same TeX interline rule, so spacing is unchanged).
//   2. Fetched blocks. A block may carry data-nodelist-src (a same-origin
//      URL) instead of data-nodelist-b64; the viewer fetches the bytes.
//      Pages whose blocks exceed the embed budget use this.
//   3. Reflow events. After the first paint and after every re-layout the
//      block dispatches a bubbling "latex-viewer:reflow" CustomEvent so
//      the page's card-placement script can re-join cards to anchors.
//   4. renderNodes gained a no-ink `mark` case that reports the pen
//      position to sinks declaring a `marker` method and never advances;
//      sinks without one (paint, ink measurement) skip markers entirely.
//   5. No protobuf.js. Upstream decodes blocks through protobuf.js
//      reflection, whose decoder is built by runtime code generation
//      (Function(...)) — forbidden under this site's CSP (script-src
//      'self', no 'unsafe-eval'). The schema generations this viewer
//      renders are pinned anyway (supported-schemas.json — the build
//      drops others to the PDF-only page), so blocks are decoded by the
//      fixed-schema proto2 wire decoder below and protobuf.min.js is not
//      shipped at all. The #latex-schema island stays embedded as the
//      page's self-description; nothing parses it at runtime.
//   6. Equation numbers. layoutDisplaySegment lifts a row's number out
//      before centring (the \eqno box, or amsmath's trailing tag cell in
//      an alignment row) and places it the way amsmath does: flush with
//      the column edge beside the equation when the centred body leaves
//      room, else on a line of its own. The body is centred whenever it
//      fits and the scroll box counts the body alone, so the number is
//      always in view (splitEquationNumber, layoutDisplaySegment).
//   7. Wide pictures and rules. A picture standing in a paragraph that is
//      wider than the column is scaled down to fit, uniformly, and its
//      line metrics with it; recomputed on every reflow (pictureFit,
//      fitPictures). A picture's advance may be the kern after a
//      zero-width box (pgf), which scales with it (pictureUnits, kW); a
//      line KP cannot break — a figure's panels side by side — takes one
//      scale for all its pictures, so their composition survives. A lone
//      rule (\hrule width\hsize, the footnote rule) is fitted the same
//      way, in a paragraph or as a rule-line display (loneRule, rW).
//   8. First paint waits for the fonts. Faces are registered through the
//      FontFace API and a block paints only once its faces have loaded (or
//      3 s have passed); the layout, and so the block's height, is done
//      first (registerFonts, initBlock).
//   9. Both indents of a \parshape band. A paragraph's right inset (an
//      abstract, a quote) is recovered from the widest band in the
//      document and kept, like the left one (paraBand).
//  10. \parbox paragraphs. A paragraph whose only ink is a vlist of
//      compile-time lines (a LIPIcs caption) is rebuilt as running text
//      before layout, so KP re-breaks it at the column
//      (unboxPresetParagraphs).
//  11. Scroll cue. A display's scroll box sits in a .latex-display-frame
//      whose data-scroll names the edge(s) it can still pan toward; the
//      stylesheet fades those edges (noteScrollEdges).
//  12. Footnotes. The schema carries a footnote's reference point as an
//      `fnref` node (in a paragraph) or a `footnote_ref` item (between
//      flow items), and its text as ordinary paragraphs at the end of the
//      stream with Paragraph.footnote = k. The reference points take the
//      marker anchor path exactly — a zero-size element
//      <span class="latex-anchor latex-fnref" data-footnote="k"
//      id="fn-ref-k"> at the pen position, re-placed on every reflow. The
//      footnote's paragraphs are laid out and painted as before (they are
//      the endnotes fallback) but each footnote is its own text segment,
//      whose element carries class latex-footnote and data-footnote="k",
//      and the rule display in front of the first one carries
//      latex-footnote-rule — so a page with a margin rail can lift the
//      segments out as sidenotes and hide the rule. Such a page states the
//      sidenotes' measure in data-latex-footnote-width (CSS px) on the
//      block, and footnote segments are then laid out at that width
//      instead of the column's; reflowBlock treats a change of it like a
//      change of width, and window.laxLatexViewer.reflow(el) lets the page
//      ask for that re-layout (a no-op when nothing changed).
//
// Upstream header follows.
//
// Finds every [data-nodelist-b64] element on the page and renders it as an
// inline SVG using Knuth-Plass line breaking.
//
// Data is embedded in the HTML at Hugo build time (via prebuild.py).
// No runtime fetching of binary files — works fully offline.

(function () {
'use strict';

// Version marker for cache diagnosis: logs the ?v= content hash the page
// requested, and stamps <html data-latex-viewer> when colour maps install.
const BUILD = (document.currentScript?.src.match(/v=([a-f0-9]+)/) || [])[1] || 'unversioned';
console.log(`[latex-viewer] build ${BUILD}`);

// ── Fixed rendering constants ─────────────────────────────────────────────────

const ZOOM         = 2;
const SP_TO_PX     = ZOOM / 65536;
const RUNNING_RULE = -1073741824;

// ── KP algorithm defaults (overridable per-block via data attributes) ─────────

const DEFAULT_BLEED_PX               = 10;
const DEFAULT_ALIGN                  = 'justify'; // 'justify' | 'left' | 'right' | 'center'

const DEFAULT_LINE_PENALTY           = 10;
const DEFAULT_ADJ_DEMERITS           = 10000;
const DEFAULT_DOUBLE_HYPHEN_DEMERITS = 10000;
const DEFAULT_PRETOLERANCE           = 100;
const DEFAULT_TOLERANCE              = 200;
const DEFAULT_TOLERANCE_2            = 500;
const DEFAULT_EMERGENCY_TOLERANCE    = 10000;
const DEFAULT_LAST_LINE_MIN          = 0.25;
const DEFAULT_LAST_LINE_PENALTY      = 100000;
const DEFAULT_MAX_EXPAND             = 0.02;
const DEFAULT_MAX_SHRINK             = 0.02;
const DEFAULT_MIN_GAP                = 16;   // pt
const DEFAULT_PAD                    = 2;    // pt (only when spacing > min gap)
const DEFAULT_USE_PROTRUSION         = true;
const DEFAULT_USE_EXPANSION          = true;
const DEFAULT_WIDTH_PT               = 400;

const RIGHT_PROTRUSION = { 44:0.7,46:0.7,58:0.5,59:0.5,45:0.5,8208:0.5,8722:0.5,33:0.3,63:0.3 };
const LEFT_PROTRUSION  = { 40:0.3,8220:0.7,8216:0.7 };

// ── Colour substitution maps ─────────────────────────────────────────────────
// Displayed values per theme, keyed by the colour LaTeX produced (lowercase
// hex). Colours not listed render as-is. Each non-light theme is matched by
// its class name on <html>; adding a theme = a new key here plus a class the
// page switcher can set. Rendering uses CSS custom properties, so theme
// switches restyle already-rendered SVG without any re-rendering.
//
// '#000000' is special: it is the DEFAULT text colour (the serializer omits
// colour on black glyphs, so they carry no inline fill). When a theme maps
// it, all default-coloured LaTeX text uses that value; when absent, default
// text falls back to the page's currentColor (as in the dark theme, where
// the page already provides a light text colour).
const COLOR_MAPS = {
    light: {
        '#000000': '#333333',   // default text → dark grey, easier on the eyes
    },
    dark: {
        '#000000': '#e7e5e4',   // default text → lighter grey (stone-200)
        '#ff0000': '#ff7b72',   // red   → softer red readable on dark
        '#0000ff': '#79c0ff',   // blue  → lighter blue readable on dark
        // lipicsGray is a *muted* accent: dark grey on the paper's white. On a
        // near-black page the same role needs the mirror image — a grey lifted
        // well clear of the background (7.2:1) but still dimmer than the body
        // text, so it stays an accent. The faint cool cast of the original is
        // kept.
        '#4f4f54': '#9c9ca3',   // lipicsGray → lifted cool grey
        // lipicsYellow is a highlight *drawn under text*, so it is the one
        // colour that must be read against the default text rather than the
        // page. Left bright it scores 1.26:1 against this theme's near-white
        // text — the paper gets away with it only because its text is black
        // (8:1). Dimmed to the brightest amber that still clears 4.5:1 (4.98),
        // so it stays recognisably yellow. The other themes keep dark text on
        // it and need no override.
        '#fcc712': '#7a5c00',   // lipicsYellow → dark amber, readable under text
    },
    sepia: {
        '#000000': '#453a26',   // default text → dark warm brown
        '#ff0000': '#c02d0c',   // red   → vivid rust, clearly not text
        '#0000ff': '#155e97',   // blue  → strong cool blue, clearly not text
        '#4f4f54': '#544f45',   // lipicsGray → same darkness, warmed to the page
    },
    contrast: {
        '#000000': '#000000',   // default text → true black
        '#ff0000': '#b30000',   // red   → darker for contrast on white
        '#0000ff': '#0000b3',   // blue  → darker for contrast on white
        // No lipicsGray override: the class's own #4f4f54 already scores 8.2:1
        // on white. The entry that used to be here existed only to darken the
        // washed-out grey this pipeline had before.
    },
};

// The page background behind a LaTeX block, per theme. TeX has no notion of the
// page's colour, so `white` in a drawing does not mean the colour white — it
// means "the paper", i.e. whatever the reader sees behind the figure. Pinning it
// to #ffffff is right only by coincidence on a white page and turns into white
// blobs on a dark one.
//
// These track the page: <main> inherits the body's background, which the theme
// classes set (see assets/css/main.css and layouts/_default/baseof.html). If the
// page's palette changes, these must follow.
const PAGE_BG = {
    light:    '#fafaf9',   // body bg-stone-50
    dark:     '#0c0a09',   // body dark:bg-stone-950
    sepia:    '#f4ecd8',   // html.sepia body
    contrast: '#ffffff',   // html.contrast body
};

// Colours TeX produced by mixing a base colour into the page: `red!20!white` is
// red at 20% over the paper. TeX resolves that to flat RGB at compile time, so
// what arrives is #ffcccc with no trace of how it was built — and a tint of a
// white page is unreadable on a dark one. Re-deriving the mix at runtime keeps
// the intent: a tint follows both its base colour and the current background.
//
// This is not the same as opacity, and must not be reimplemented with it: these
// fills are opaque on purpose, because they mask the drawing underneath.
//
// Each entry is  baked-hex: [base colour, percentage of base].
const TINTS = {
    '#ffcccc': ['#ff0000', 20],   // red!20!white         — live intervals, scopes
    '#ccccff': ['#0000ff', 20],   // blue!20!white        — live intervals, scopes
    '#fef4d0': ['#fcc712', 20],   // lipicsYellow!20!white — scopes
    '#808080': ['#000000', 50],   // black!50!white       — muted labels
};

function colorFill(c) {
    return `var(--latex-color-${c.slice(1)}, ${c})`;
}

let colorMapsInstalled = false;
function installColorMaps() {
    if (colorMapsInstalled) return;
    colorMapsInstalled = true;
    let css = '';
    for (const theme of new Set([...Object.keys(COLOR_MAPS), ...Object.keys(PAGE_BG)])) {
        const decls = Object.entries(COLOR_MAPS[theme] ?? {})
            .map(([src, dst]) => `  --latex-color-${src.slice(1)}: ${dst};`);
        if (PAGE_BG[theme]) decls.push(`  --latex-page-bg: ${PAGE_BG[theme]};`);
        if (decls.length === 0) continue;
        const sel = theme === 'light' ? ':root' : `:root.${theme}`;
        css += sel + ' {\n' + decls.join('\n') + '\n}\n';
    }

    // Derived colours. These are theme-independent declarations: every term is
    // itself a themed variable, so the browser recomputes them on a theme switch
    // with no re-render. They sit on :root, where the theme classes also live, so
    // var() resolves against the *same* element's themed values.
    //
    // The light theme's own block is a plain :root too, and comes first, so these
    // must not restate anything COLOR_MAPS sets, or they would win for light only.
    const derived = ['  --latex-color-ffffff: var(--latex-page-bg);'];
    for (const [hex, [base, pct]] of Object.entries(TINTS)) {
        derived.push(`  --latex-color-${hex.slice(1)}: color-mix(in srgb, `
                   + `var(--latex-color-${base.slice(1)}, ${base}) ${pct}%, `
                   + `var(--latex-page-bg));`);
    }
    css += ':root {\n' + derived.join('\n') + '\n}\n';
    // Default-coloured glyphs carry no inline fill; route them through the
    // '#000000' variable with currentColor as fallback. The html prefix
    // outranks the page's own `.latex-block svg text` rule regardless of
    // stylesheet order.
    //
    // Deliberately not 'rect': rules set their fill inline, and this rule's
    // specificity would otherwise reach inside a tikzpicture and repaint every
    // coloured shape in the drawing as text.
    css += 'html .latex-block svg text, html .latex-block svg tspan '
         + '{ fill: var(--latex-color-000000, currentColor); }\n';
    const s = document.createElement('style');
    s.textContent = css;
    document.head.appendChild(s);
    document.documentElement.setAttribute('data-latex-viewer', BUILD);
}

// ── Per-block params ──────────────────────────────────────────────────────────

// Read the current alignment for an element: CSS custom property wins over data attr.
// Called both at mount time and on every resize so media-query changes are picked up.
// lax: the measure a page sets for the footnote segments it lifts into a
// margin rail — data-latex-footnote-width, in CSS px like clientWidth (so
// the page can stamp what it measured), converted to pt as the column's
// width is. 0 (absent, or unparseable) means the column's own width.
function footnoteWidthFromEl(el) {
    const px = parseFloat(el.dataset.latexFootnoteWidth);
    return Number.isFinite(px) && px > 0 ? px / ZOOM : 0;
}

function alignFromEl(el) {
    const css = getComputedStyle(el).getPropertyValue('--latex-align').trim();
    return css || el.dataset.align || DEFAULT_ALIGN;
}

function paramsFromEl(el) {
    const d   = el.dataset;
    const num  = (key, def) => key in d ? parseFloat(d[key]) : def;
    const bool = (key, def) => key in d ? d[key] !== 'false'  : def;
    return {
        linePenalty:          num('linePenalty',          DEFAULT_LINE_PENALTY),
        adjDemerits:          num('adjDemerits',          DEFAULT_ADJ_DEMERITS),
        doubleHyphenDemerits: num('doubleHyphenDemerits', DEFAULT_DOUBLE_HYPHEN_DEMERITS),
        pretolerance:         num('pretolerance',         DEFAULT_PRETOLERANCE),
        tolerance:            num('tolerance',            DEFAULT_TOLERANCE),
        tolerance2:           num('tolerance2',           DEFAULT_TOLERANCE_2),
        emergencyTolerance:   num('emergencyTolerance',   DEFAULT_EMERGENCY_TOLERANCE),
        lastLineMin:          num('lastLineMin',          DEFAULT_LAST_LINE_MIN),
        lastLinePenalty:      num('lastLinePenalty',      DEFAULT_LAST_LINE_PENALTY),
        maxExpand:            num('maxExpand',            DEFAULT_MAX_EXPAND),
        maxShrink:            num('maxShrink',            DEFAULT_MAX_SHRINK),
        minGapPt:             num('minGap',               DEFAULT_MIN_GAP),
        padPt:                num('pad',                  DEFAULT_PAD),
        useProtrusion:        bool('protrusion',          DEFAULT_USE_PROTRUSION),
        useExpansion:         bool('expansion',           DEFAULT_USE_EXPANSION),
        bleedPx:              num('bleedPx',              DEFAULT_BLEED_PX),
        align:                alignFromEl(el),
    };
}

// ── Per-page shared state ─────────────────────────────────────────────────────

// fontInfo is intentionally NOT global — font IDs are per-compilation and collide
// across blocks (e.g. both block 1 and block 2 may use ID 54 for different files).
// Each block gets its own map returned from registerFonts().
const registeredFontFaces = new Set();
let   fontUrlMap          = {};     // original font filename → served filename (see loadFontMap)
let   fontBase            = '/fonts/'; // @font-face src base; override via #latex-font-map[data-fonts-base] for sites served under a subpath (e.g. GitHub Pages project sites)
let   fontsPending        = false;  // a face still had to be fetched at first paint (see registerFonts / init)

// Per-block cache so ResizeObserver can re-render without re-decoding.
// cache holds width-independent layout state (break candidates) and the
// previously rendered SVG so resize can move elements instead of recreating.
const blockData = new WeakMap(); // el → { doc, lastWidth, lastAlign, params, cache }

// Re-layout one block for its current width/alignment. Returns false if nothing
// needed doing (so the caller can stay quiet).
function reflowBlock(el) {
    const data = blockData.get(el);
    if (!data) return false;
    // A block inside a collapsed section is display:none and reports clientWidth
    // 0, which would fall through to DEFAULT_WIDTH_PT and re-lay-out the block at
    // a width it is never shown at — leaving that stale layout to be printed.
    // Keep the last good layout; being shown again resizes the element, which
    // fires the observer once more.
    if (el.clientWidth === 0 && !el.dataset.latexWidth) return false;
    const newWidth = el.dataset.latexWidth
        ? parseInt(el.dataset.latexWidth)
        : (el.clientWidth / ZOOM) || DEFAULT_WIDTH_PT;
    // Re-read alignment every time: a media query may have changed --latex-align.
    const newAlign = alignFromEl(el);
    // lax: the sidenote measure too (see footnoteWidthFromEl).
    const newFnWidth = footnoteWidthFromEl(el);
    if (Math.abs(newWidth - data.lastWidth) < 0.5 && newAlign === data.lastAlign
        && Math.abs(newFnWidth - data.lastFnWidth) < 0.5) return false;
    data.lastWidth = newWidth;
    data.lastAlign = newAlign;
    data.lastFnWidth = newFnWidth;
    const params = { ...data.params, align: newAlign, footnoteWidthPt: newFnWidth };
    const t0  = performance.now();
    // Layout always runs for the whole block so its height (and the page's scroll
    // geometry) stays correct — it is pure computation and cheap. Painting, the
    // DOM-heavy part, is then gated to the visible segments.
    const root = layoutDocument(data.fontInfo, data.doc, newWidth, params, data.cache);
    if (root !== el.firstElementChild) el.replaceChildren(root);
    // Re-layout moved every line: painted segments now hold ink at stale positions.
    // Mark them dirty so they get re-drawn in place — the on-screen ones now (below),
    // each off-screen one when it next scrolls into view (segIO). They are never
    // hidden in the meantime: their <svg> keeps its new reserved size, only its
    // glyphs are stale until repainted.
    for (const s of data.cache.dom.segs) if (s.painted) s.dirty = true;
    const tp = performance.now();
    const repainted = paintVisibleNow(data.fontInfo, data.cache);
    const st = data.cache.stats || {};
    // lax: re-anchor the markers at the new layout, then tell the page.
    placeAnchors(data.cache);
    el.dispatchEvent(new CustomEvent('latex-viewer:reflow', { bubbles: true }));
    console.log(`[latex-viewer] re-render at ${newWidth.toFixed(0)}pt: layout ${(tp - t0).toFixed(1)} ms, paint ${(performance.now() - tp).toFixed(1)} ms (${repainted} visible segment(s); ${st.repositioned||0} repositioned, ${st.created||0} created)`);
    return true;
}

// Rebuild a block's DOM from scratch at its current width and repaint the visible
// segments. Used when webfonts finish loading after the first paint: the layout is
// unchanged (it is computed from the document's embedded glyph metrics, never the
// browser font), but discarding cache.dom forces layoutDocument to create fresh
// elements, which is what makes the browser rasterise the glyphs with the
// now-loaded face instead of the fallback it painted first. Break candidates
// (cache.bcs) survive, so this costs a layout pass and a visible-segment repaint,
// not a re-decode.
function rerenderBlock(el) {
    const data = blockData.get(el);
    if (!data) return;
    // Rebuilding makes fresh <svg>s, so stop observing the old ones (segIO would
    // otherwise hold detached elements). layoutDocument observes the new ones.
    if (data.cache.dom) for (const s of data.cache.dom.segs) segIO.unobserve(s.svg);
    data.cache.dom = null;
    data.cache.layout = null;
    const params = { ...data.params, align: data.lastAlign, footnoteWidthPt: data.lastFnWidth };
    el.replaceChildren(layoutDocument(data.fontInfo, data.doc, data.lastWidth, params, data.cache));
    paintVisibleNow(data.fontInfo, data.cache);
    // lax: the rebuild made fresh anchor elements; re-place and re-announce.
    placeAnchors(data.cache);
    el.dispatchEvent(new CustomEvent('latex-viewer:reflow', { bubbles: true }));
}

// Repaint every block after a wave of webfonts finishes loading. On a cold cache
// faces arrive in waves *after* content has painted — at init, and lazily on
// scroll — and SVG <text> does not reliably re-rasterise when its face lands
// (Firefox especially). A one-shot repaint on document.fonts.ready is not enough:
// a heading below the first screen is not painted until scrolled to, so if it is
// reached while its (bold) face is still loading it paints in a fallback that the
// already-fired repaint never revisits. So repaint on every loadingdone wave, not
// just once. rerenderBlock also clears the cached elements, so segments painted
// later on scroll are fresh too. Coalesced to one frame; the listener detaches
// once every face has settled. Wired up (see init) only when a face was still
// pending at first paint, so a warm load does none of this.
let fontRepaintScheduled = false;
function scheduleFontRepaint() {
    if (fontRepaintScheduled) return;
    fontRepaintScheduled = true;
    requestAnimationFrame(() => {
        fontRepaintScheduled = false;
        for (const el of observedBlocks) rerenderBlock(el);
        if (document.fonts && document.fonts.status === 'loaded' && document.fonts.removeEventListener) {
            document.fonts.removeEventListener('loadingdone', scheduleFontRepaint);
        }
    });
}

// Re-layout runs in a rAF, not synchronously in the observer callback. Doing the
// work inline resizes the observed element (a new layout has a new height), which
// the observer then reports as "ResizeObserver loop completed with undelivered
// notifications" — harmless but noisy. Deferring to the next frame breaks that
// synchronous feedback loop and coalesces bursts of resizes into one pass.
const roPending = new Set();
let roScheduled = false;
const ro = new ResizeObserver(entries => {
    for (const entry of entries) roPending.add(entry.target);
    if (roScheduled) return;
    roScheduled = true;
    requestAnimationFrame(() => {
        roScheduled = false;
        const els = [...roPending];
        roPending.clear();
        for (const el of els) reflowBlock(el);
    });
});

// ── Per-segment painting (grow-only) ──────────────────────────────────────────
// Layout always covers the whole block (cheap pure computation, and it must, so
// the block's height keeps scroll geometry exact). Painting — placing tens of
// thousands of glyph elements — is the DOM-heavy part, so a segment is painted
// only once it comes within a viewport of the screen. Which segments those are is
// tracked by an IntersectionObserver on each segment's own <svg>, i.e. from the
// real element positions. It is deliberately NOT computed from a running height
// model: a painted display's actual height includes padding reserved for the ink
// that overhangs its box (see paintSegment), which such a model cannot predict, so
// it drifts from the real layout and, near the bottom of a long page, mis-gates
// segments that are in fact on screen. Observing the elements has no such drift and
// costs no per-frame measurement.
//
// Painting is grow-only: a segment, once painted, is never hidden. Scrolling can
// only ever add ink, never remove it, so text never vanishes as the page moves. A
// width change re-draws the painted segments in place (their glyphs move) — the
// visible ones at once, the rest when scrolled to — but still never blanks them.
const observedBlocks = new Set();       // blocks (for font-repaint + print)
const segRef = new WeakMap();           // a segment's <svg> → { cache, i }
const segIO = new IntersectionObserver(entries => {
    for (const e of entries) {
        const ref = segRef.get(e.target);
        const s = ref && ref.cache.dom && ref.cache.dom.segs[ref.i];
        if (!s) continue;
        s.intersecting = e.isIntersecting;
        // lax: not while the block's first paint is held for its fonts (see
        // initBlock) — the hold's release paints the visible set itself.
        if (ref.cache.holdPaint) continue;
        if (e.isIntersecting && (!s.painted || s.dirty)) paintSegment(ref.cache.fontInfo, ref.cache, ref.i);
    }
}, { rootMargin: '100% 0px' });         // one-viewport vertical lookahead

// Observe each not-yet-observed segment of a block. Idempotent: a segment's <svg>
// is created once and reused across reflows, so its observation persists (only a
// font rerender, which rebuilds the DOM, makes new ones — see rerenderBlock).
function observeSegments(cache) {
    const segs = cache.dom.segs;
    for (let i = 0; i < segs.length; i++) {
        const s = segs[i];
        if (s.observed) continue;
        segRef.set(s.svg, { cache, i });
        segIO.observe(s.svg);
        s.observed = true;
    }
}

// Paint, synchronously, every segment that needs it (never painted, or dirtied by
// a reflow) and is within a viewport of the screen. Reads each segment's real box,
// so it shares the IntersectionObserver's immunity to height drift and is correct
// under page zoom (getBoundingClientRect and innerHeight are the same space). Two
// passes — measure all, then paint — because painting mutates the DOM and would
// otherwise force a fresh layout between measurements. Used for the first paint and
// after a reflow; the observer covers whatever scrolls into view later.
function paintVisibleNow(fontInfo, cache) {
    if (!cache.dom || cache.holdPaint) return 0;   // lax: held for fonts, see initBlock
    cache.stats = { created: 0, moved: 0, repositioned: 0, removed: 0 };
    const segs = cache.dom.segs;
    const vh = window.innerHeight || 800, M = vh;
    const todo = [];
    for (let i = 0; i < segs.length; i++) {
        const s = segs[i];
        if (s.painted && !s.dirty) continue;
        const r = s.svg.getBoundingClientRect();
        if (r.bottom > -M && r.top < vh + M) todo.push(i);
    }
    for (const i of todo) paintSegment(fontInfo, cache, i);
    return todo.length;
}

let vpScheduled = false;
function scheduleViewportPaint() {
    if (vpScheduled) return;
    vpScheduled = true;
    requestAnimationFrame(() => {
        vpScheduled = false;
        for (const el of observedBlocks) {
            const data = blockData.get(el);
            if (data) paintVisibleNow(data.fontInfo, data.cache);
        }
    });
}
// Scrolling is handled by the IntersectionObserver (no per-frame work). A viewport
// resize — or the synthetic resize the zoom control fires — can change which
// segments are on screen without the observer necessarily re-firing, so re-check
// the visible set then.
window.addEventListener('resize', scheduleViewportPaint, { passive: true });

// Print needs every segment painted (off-screen ones are empty until then). Grow-
// only means they simply stay painted afterwards, so there is nothing to restore.
window.addEventListener('beforeprint', () => {
    for (const el of observedBlocks) {
        const data = blockData.get(el);
        if (data) paintDocument(data.fontInfo, data.cache);
    }
});

// ── Helpers ───────────────────────────────────────────────────────────────────

function b64ToBytes(b64) {
    return Uint8Array.from(atob(b64), c => c.charCodeAt(0));
}

// ── Font loading ──────────────────────────────────────────────────────────────

// lax: the faces this page has registered, by the font's original filename,
// so a later block that shares a face can wait on the same load; and how
// long a first paint waits for its faces before going ahead in a fallback.
const fontFaces    = new Map();     // file → FontFace
const FONT_WAIT_MS = 3000;

// lax: registration is synchronous and returns the readiness promise
// separately, so a block can be laid out (its height reserved) while its
// faces are still in flight and painted only once they have arrived.
//
// Faces are created through the FontFace API rather than an injected
// @font-face stylesheet. A CSS-declared face joins document.fonts only at
// the next style recalculation, so document.fonts.load() and .check() run
// straight after the injection matched nothing: load() resolved at once,
// check() reported true, and the first paint went ahead — every glyph in a
// fallback serif, repainted a moment later when the real face landed, with
// the block's scroll-box padding measured off the wrong ink. A FontFace
// added to document.fonts is matchable immediately and carries its own
// load promise, so the wait is for the actual bytes.
function registerFonts(fontsData) {
    const fontInfo = {};
    const fileToFamily = {};
    const faces = [];
    let css = '';
    for (const f of Object.values(fontsData)) {
        const file = f.filename;
        if (fileToFamily[file]) continue;
        // A font the serializer could not resolve to an OTF file (filename
        // 'unknown' — e.g. a Type1 math font with no OpenType form) has nothing to
        // fetch. Map it to a system serif so its glyphs fall back, rather than
        // emitting an @font-face that is guaranteed to 404.
        if (!file || file === 'unknown') { fileToFamily[file] = 'serif'; continue; }
        // The family is keyed off the font's *original* name (its stable identity
        // across blocks); the file it is fetched from comes from the font map,
        // which for a modified font is a renamed, content-hashed file (the map is
        // empty on pages that don't ship it, so it falls back to the name as-is).
        const family  = file.replace(/\.otf$/i, '').replace(/[^a-zA-Z0-9]/g, '_');
        const servedFile = fontUrlMap[file] || file;
        const src = `url('${fontBase}${servedFile}')`;
        if (!registeredFontFaces.has(file)) {
            registeredFontFaces.add(file);
            if (typeof FontFace === 'function' && document.fonts && document.fonts.add) {
                const face = new FontFace(family, src);
                document.fonts.add(face);
                // A face that fails to load (a missing file, a network blip)
                // must not reject anything: its glyphs fall back (or are drawn
                // as metric boxes; see the sink). The rejection is observed
                // here so it is not reported as unhandled.
                face.load().catch(() => {});
                fontFaces.set(file, face);
            } else {
                css += `@font-face { font-family: '${family}'; src: ${src}; }\n`;
            }
        }
        const face = fontFaces.get(file);
        if (face) faces.push(face);
        fileToFamily[file] = family;
    }

    if (css) {
        const s = document.createElement('style');
        s.textContent = css;
        document.head.appendChild(s);
    }

    // No font-feature-settings are applied: glyphs that are not the cmap
    // default for their codepoint (script-size variants, accents, …) are
    // rewritten to dedicated PUA codepoints by prebuild.py, so every glyph
    // renders identically in every browser without relying on GSUB features.
    for (const [idStr, f] of Object.entries(fontsData)) {
        fontInfo[idStr] = {
            family:  fileToFamily[f.filename],
            size_px: (f.size_sp / 65536) * ZOOM,
            // A font with no OTF to load: its glyphs are drawn as metric boxes
            // (see the sink's glyph handler) so the missing ink is visible.
            unresolved: !f.filename || f.filename === 'unknown',
        };
    }

    const families = [...new Set(Object.values(fileToFamily))].filter(fam => fam !== 'serif');

    // Every face settled (loaded or failed), or the deadline — whichever is
    // first. A warm cache resolves this at once; a cold one holds the first
    // paint for the bytes; a stalled fetch lets the page render in fallback
    // after FONT_WAIT_MS, and the loadingdone repaint (see init) catches the
    // face when it finally lands.
    let ready;
    if (faces.length) {
        const settled = Promise.allSettled(faces.map(face => face.loaded));
        ready = Promise.race([settled, new Promise(r => setTimeout(r, FONT_WAIT_MS))]);
    } else if (families.length && document.fonts && document.fonts.load) {
        // No FontFace API: the stylesheet route, awaited as before.
        ready = Promise.allSettled(families.map(fam => document.fonts.load(`12px '${fam}'`)));
    } else {
        ready = Promise.resolve();
    }
    // Whether some face is still not loaded when the block paints — decided
    // after the wait, so it reflects the paint the reader actually sees. It
    // makes init() force a repaint when the faces do settle; a warm load,
    // where the first paint is already correct, leaves it false and pays for
    // no second render.
    const stillPending = () => faces.some(face => face.status !== 'loaded');
    return { fontInfo, ready, stillPending };
}

// ── Glyph metrics ─────────────────────────────────────────────────────────────
// A glyph's width/height/depth are interned once per distinct box in the
// document's glyph_metrics table (the encoder replaces the inline dimensions with
// a 1-based Node.metrics index — the same box repeats across thousands of glyphs,
// so keeping one copy matters at 1000-page scale). They are NOT folded back onto
// the node; instead layout/paint read them straight from the table by index,
// which is a single array lookup and keeps the nodes lean. `glyphMetrics` is
// pointed at the current block's table by layoutDocument/paintDocument before any
// node is touched; both entry points re-point it, so deferred paints and
// interleaved blocks always read their own table.
let glyphMetrics = null;
function useGlyphMetrics(table) {
    glyphMetrics = table || [];
    // A decoded entry may lack a zero dimension (an absent field decodes to
    // undefined); fill it in once (per block) or the reader would get undefined
    // and poison the layout arithmetic. Idempotent.
    for (const m of glyphMetrics) {
        if (m.width  === undefined) m.width  = 0;
        if (m.height === undefined) m.height = 0;
        if (m.depth  === undefined) m.depth  = 0;
    }
}
// Read from the table by index; but if a glyph still carries inline dimensions
// (an un-interned document — e.g. output.json fed straight to layout by a test
// harness), honour those. The branch outcome is constant for a given document,
// so it costs nothing measurable.
const gW = n => n.width  !== undefined ? n.width  : glyphMetrics[n.metrics - 1].width;
const gH = n => n.height !== undefined ? n.height : glyphMetrics[n.metrics - 1].height;
const gD = n => n.depth  !== undefined ? n.depth  : glyphMetrics[n.metrics - 1].depth;

// lax: a picture's effective box. A picture that stands in a paragraph (a
// standalone tikzpicture under \centering, say) is a rigid node the line
// breaker cannot split, so one wider than the reader's column would be set
// at its compiled width and bleed past both edges — and the left bleed runs
// off the page, where nothing can scroll to it. Such a picture is scaled
// down to fit instead: layoutTextSegment records a uniform scale (<1) for it
// here, per layout pass, and every reader of a picture's dimensions — the
// line breaker, the line profiles, the ink measurement, the renderer and the
// paint sink — goes through these, so the drawing, its advance and the line
// metrics around it shrink together. The map is rewritten on every reflow
// (the scale depends on the column), and a picture that fits has no entry.
// The boxes that wrap a picture (graphicx puts the externalised drawing in
// an \hbox of its own size) carry the same scale, read through bW/bH/bD
// wherever a box's dimensions advance the pen or profile a line, so the
// wrapper shrinks with its picture. Pictures inside displays are not
// fitted: a display keeps its compiled width and pans in its scroll box,
// as MathJax does.
const pictureFit = new WeakMap();   // picture node, or a box wrapping one → scale
const pS = n => pictureFit.get(n) || 1;
const pW = n => (n.width  ?? 0) * pS(n);
const pH = n => (n.height ?? 0) * pS(n);
const pD = n => (n.depth  ?? 0) * pS(n);
const bW = pW, bH = pH, bD = pD;    // the same readers, named for boxes
// lax: the same scale on a kern and on a rule. pgf sets a picture as a
// zero-width box followed by a kern of the picture's width, so the kern is
// the advance that has to shrink with it (see pictureUnits); and a lone
// rule — \hrule width\hsize, a footnote rule — is fitted like a lone
// picture, its drawn width following the column (see fitPictures,
// layoutDisplaySegment). A rule's thickness is never scaled.
const kW = n => (n.kern  ?? 0) * pS(n);
const rW = n => (n.width ?? 0) * pS(n);

// ── Width helpers ─────────────────────────────────────────────────────────────

function nodeWidthSp(n) {
    switch (n.type) {
        case 'glyph':               return gW(n);
        case 'picture':             return pW(n);   // lax: fitted (see pictureFit)
        case 'kern':                return kW(n);   // lax: fitted beside a fitted picture
        // lax: a rule standing in the paragraph advances the pen when drawn
        // (renderNodes), so it has to count here too; fitted like a picture.
        case 'rule':                return n.width === RUNNING_RULE ? 0 : rW(n);
        case 'glue':                return n.width;
        case 'disc':                return sumWidthSp(n.replace);
        // A transform is drawing-only and has no metrics of its own; its
        // children advance the pen just as they did before being grouped.
        case 'transform':           return sumWidthSp(n.children);
        case 'hlist': case 'vlist': return bW(n);   // lax: fitted when wrapping a fitted picture
        case 'math':                return n.surround;
        default:                    return 0;
    }
}

function sumWidthSp(nodes)    { return nodes.reduce((a, n) => a + nodeWidthSp(n), 0); }
// The infinite-order fill on a line (\hfil/\hfill from \\, \hfill, or the amsthm
// QED glue) and its total stretch at that order. A line carrying one is not
// justified; instead its slack goes entirely into this glue, which is what pushes
// anything after it (a QED box, a right-flushed word) to the right margin.
function fillInfo(nodes) {
    let order = 0, stretch = 0;
    for (const n of nodes) {
        if (n.type === 'glue' && (n.stretch_order || 0) > 0) {
            const o = n.stretch_order;
            if (o > order) { order = o; stretch = n.stretch; }
            else if (o === order) stretch += n.stretch;
        }
    }
    return { order, stretch };
}
function sumRigidWidth(nodes) { return nodes.reduce((a, n) => n.type==='glyph' ? a+gW(n) : n.type==='kern' ? a+kW(n) : a, 0); }

// The set size of one glue node under a box's packing ratio.
function setGlue(g, ratio, fillOrder) {
    let w = g.width;
    if (ratio > 0 && (g.stretch_order || 0) === fillOrder && g.stretch > 0) w += ratio * g.stretch;
    else if (ratio < 0 && (g.shrink_order || 0) === fillOrder && g.shrink > 0) w += ratio * g.shrink;
    return w;
}

// A vlist's glue is *set* exactly as an hlist's is, just along y — so stacking
// its children by their natural widths is wrong wherever TeX packed the box to
// a size. Extensible delimiters are the case that makes this visible: LuaTeX
// assembles a tall \left( from GlyphAssembly pieces stacked with *negative,
// stretchable* glue so they overlap, and it is the set size that makes the
// assembly reach its declared height. Summing the raw widths instead leaves the
// bracket around a 45pt box some 11pt short of its own baseline, floating above
// the thing it is supposed to enclose.
//
// Unlike hlistGlueRatio this has no natural-size fallback: that path measures
// with nodeWidthSp, which is a *horizontal* size and means nothing in a vlist.
// TeX fills in glue_set/glue_sign on every box it packs, so there is nothing to
// fall back for; a box without them simply has no glue to set.
function vlistGlueRatio(box) {
    if (box.glue_sign === 1 && box.glue_set > 0) return { ratio:  box.glue_set, fillOrder: box.glue_order || 0 };
    if (box.glue_sign === 2 && box.glue_set > 0) return { ratio: -box.glue_set, fillOrder: box.glue_order || 0 };
    return { ratio: 0, fillOrder: 0 };
}

function hlistGlueRatio(box) {
    if (box.glue_sign === 1 && box.glue_set > 0) return { ratio:  box.glue_set, fillOrder: box.glue_order || 0 };
    if (box.glue_sign === 2 && box.glue_set > 0) return { ratio: -box.glue_set, fillOrder: box.glue_order || 0 };
    const nodes = box.children;
    let natural = 0;
    const stretch = [0,0,0,0], shrink = [0,0,0,0];
    for (const n of nodes) {
        if (n.type === 'glue') { natural += n.width; stretch[n.stretch_order||0] += n.stretch; shrink[n.shrink_order||0] += n.shrink; }
        else { natural += nodeWidthSp(n); }
    }
    const slack = box.width - natural;
    if (slack > 0) { for (let o=3;o>=0;o--) if (stretch[o]>0) return { ratio: slack/stretch[o], fillOrder:o }; }
    else if (slack < 0) { for (let o=3;o>=0;o--) if (shrink[o]>0)  return { ratio: slack/shrink[o],  fillOrder:o }; }
    return { ratio: 0, fillOrder: 0 };
}

// ── Protrusion ────────────────────────────────────────────────────────────────

function findLastGlyph(nodes, idx)  { for(let k=idx-1;k>=0;k--){ const n=nodes[k]; if(n.type==='kern'||n.type==='penalty') continue; return n.type==='glyph'?n:null; } return null; }
function findFirstGlyph(nodes, idx) { for(let k=idx;k<nodes.length;k++){ const n=nodes[k]; if(n.type==='kern'||n.type==='penalty'||n.type==='local_par') continue; return n.type==='glyph'?n:null; } return null; }
function rightProtrusionOf(g) { return g ? (RIGHT_PROTRUSION[g.char]||0)*gW(g) : 0; }
function leftProtrusionOf(g)  { return g ? (LEFT_PROTRUSION [g.char]||0)*gW(g) : 0; }

// ── Knuth-Plass: break candidates ────────────────────────────────────────────

function buildBreakCandidates(nodes) {
    const bcs = [{
        kind:'start', nodeIdx:-1, penalty:0,
        preW:0, postW:0, replaceW:0, preGlyphW:0, postGlyphW:0, replaceGlyphW:0,
        spaceW:0, spaceS:0, spaceZ:0, cumW:0, cumS:0, cumZ:0, cumGlyphW:0, cumFill:0,
        rightProtrusion:0, leftProtrusion:leftProtrusionOf(findFirstGlyph(nodes,0)),
    }];
    let cumW=0, cumS=0, cumZ=0, cumGlyphW=0, cumFill=0;

    for (let i=0; i<nodes.length; i++) {
        const n = nodes[i];
        if (n.type==='local_par') continue;

        // \parfillskip (LuaTeX subtype 15) terminates the paragraph, whatever its
        // stretch. The usual value is "0pt plus 1fil" (a ragged last line), but
        // \centering / \raggedleft set it rigid ("0pt") — and keying the end on
        // stretch>0, as before, gave a centred paragraph (a title, \begin{center})
        // no end candidate at all: kpPass then returned nothing and the greedy
        // fallback emitted no final line, so the whole paragraph vanished whenever
        // it happened to fit on one line. Key on the subtype instead.
        if (n.type==='glue' && n.subtype===15) {
            bcs.push({ kind:'end', nodeIdx:i, penalty:-10000, preW:0,postW:0,replaceW:0, preGlyphW:0,postGlyphW:0,replaceGlyphW:0, spaceW:0,spaceS:0,spaceZ:0, cumW,cumS,cumZ,cumGlyphW,cumFill, rightProtrusion:rightProtrusionOf(findLastGlyph(nodes,i)), leftProtrusion:0 });
            break;
        }
        // A mid-paragraph infinite fill (the \hfil that \\ inserts before its
        // forced break, or an explicit \hfill) is not the end: it marks the line
        // that contains it as "filled" (cumFill), so its slack is absorbed there
        // rather than justified, exactly like a last line. Treating the first such
        // fill as the end would silently drop everything after a \\.
        if (n.type==='glue' && n.stretch_order>0) {
            cumW+=n.width; cumFill+=1;
            continue;
        }
        if (n.type==='glue' && n.subtype===13) {
            bcs.push({ kind:'space', nodeIdx:i, penalty:0, preW:0,postW:0,replaceW:0, preGlyphW:0,postGlyphW:0,replaceGlyphW:0, spaceW:n.width,spaceS:n.stretch,spaceZ:n.shrink, cumW,cumS,cumZ,cumGlyphW,cumFill, rightProtrusion:rightProtrusionOf(findLastGlyph(nodes,i)), leftProtrusion:leftProtrusionOf(findFirstGlyph(nodes,i+1)) });
            cumW+=n.width; cumS+=!n.stretch_order?n.stretch:0; cumZ+=!n.shrink_order?n.shrink:0;
        } else if (n.type==='disc') {
            const preW=sumWidthSp(n.pre),postW=sumWidthSp(n.post),replaceW=sumWidthSp(n.replace);
            const preGlyphW=sumRigidWidth(n.pre),postGlyphW=sumRigidWidth(n.post),replaceGlyphW=sumRigidWidth(n.replace);
            const preGs=n.pre.filter(x=>x.type==='glyph'), postGs=n.post.filter(x=>x.type==='glyph');
            bcs.push({ kind:'disc', nodeIdx:i, penalty:50, preW,postW,replaceW, preGlyphW,postGlyphW,replaceGlyphW, spaceW:0,spaceS:0,spaceZ:0, cumW,cumS,cumZ,cumGlyphW,cumFill, rightProtrusion:rightProtrusionOf(preGs.length>0?preGs[preGs.length-1]:findLastGlyph(nodes,i)), leftProtrusion:leftProtrusionOf(postGs.length>0?postGs[0]:findFirstGlyph(nodes,i+1)) });
            cumW+=replaceW; cumGlyphW+=replaceGlyphW;
        } else if (n.type==='penalty' && n.penalty<10000) {
            let lgW=0,lgS=0,lgZ=0,firstAfterLG=i+1;
            for (let k=i+1;k<nodes.length;k++) {
                const m=nodes[k];
                if (m.type==='kern') { lgW+=kW(m); firstAfterLG=k+1; }
                else if (m.type==='glue') { lgW+=m.width; lgS+=!m.stretch_order?m.stretch:0; lgZ+=!m.shrink_order?m.shrink:0; firstAfterLG=k+1; }
                else break;
            }
            bcs.push({ kind:'penalty', nodeIdx:i, penalty:n.penalty, preW:0,postW:0,replaceW:0, preGlyphW:0,postGlyphW:0,replaceGlyphW:0, spaceW:0,spaceS:0,spaceZ:0, cumW,cumS,cumZ,cumGlyphW,cumFill, leadingGlueW:lgW,leadingGlueS:lgS,leadingGlueZ:lgZ, rightProtrusion:rightProtrusionOf(findLastGlyph(nodes,i)), leftProtrusion:leftProtrusionOf(findFirstGlyph(nodes,firstAfterLG)) });
        } else {
            cumW+=nodeWidthSp(n);
            if (n.type==='glyph') cumGlyphW+=gW(n);
            else if (n.type==='kern') cumGlyphW+=kW(n);
            if (n.type==='glue') { cumS+=!n.stretch_order?n.stretch:0; cumZ+=!n.shrink_order?n.shrink:0; }
        }
    }
    return bcs;
}

function lineStartW(bc)      { if(bc.kind==='start') return 0; if(bc.kind==='space') return bc.cumW+bc.spaceW;   if(bc.kind==='disc') return bc.cumW+bc.replaceW-bc.postW; return bc.cumW+(bc.leadingGlueW||0); }
function lineEndW(bc)        { if(bc.kind==='disc')  return bc.cumW+bc.preW; return bc.cumW; }
function lineStartS(bc)      { if(bc.kind==='start') return 0; if(bc.kind==='space') return bc.cumS+bc.spaceS;   if(bc.kind==='penalty') return bc.cumS+(bc.leadingGlueS||0); return bc.cumS; }
function lineStartZ(bc)      { if(bc.kind==='start') return 0; if(bc.kind==='space') return bc.cumZ+bc.spaceZ;   if(bc.kind==='penalty') return bc.cumZ+(bc.leadingGlueZ||0); return bc.cumZ; }
function lineStartGlyphW(bc) { if(bc.kind==='start') return 0; if(bc.kind==='space') return bc.cumGlyphW;        if(bc.kind==='disc')    return bc.cumGlyphW+bc.replaceGlyphW-bc.postGlyphW; return bc.cumGlyphW; }
function lineEndGlyphW(bc)   { if(bc.kind==='disc')  return bc.cumGlyphW+bc.preGlyphW; return bc.cumGlyphW; }

function lineMetrics(bcA, bcB, p) {
    const protrude = p.useProtrusion ? bcA.leftProtrusion + bcB.rightProtrusion : 0;
    const w  = lineEndW(bcB) - lineStartW(bcA) - protrude;
    const s0 = bcB.cumS - lineStartS(bcA);
    const z0 = bcB.cumZ - lineStartZ(bcA);
    if (p.useExpansion) {
        const gW = lineEndGlyphW(bcB) - lineStartGlyphW(bcA);
        return { w, s: s0+gW*p.maxExpand, z: z0+gW*p.maxShrink };
    }
    return { w, s:s0, z:z0 };
}

function badness(shortage, total) {
    if (shortage===0) return 0; if (total<=0) return 10000;
    const r=shortage/total; return Math.min(10000, Math.round(100*r*r*r));
}

// ── KP DP (one pass) ─────────────────────────────────────────────────────────

function kpPass(bcs, lineWidthSp, threshold, allowDisc, p) {
    const N=bcs.length;
    const dp=Array.from({length:N},()=>[null,null,null,null]);
    dp[0][2]={demerits:0,prev_j:-1,prev_fc:-1,ratio:0,hyphenated:false};
    let minRejectedBadness=null;

    // A forced break (penalty <= -10000, e.g. from \\) is mandatory: no line may
    // span across it. lastForced[j] is the candidate index of the nearest forced
    // break before j, so a line from i to j is legal only when i >= lastForced[j].
    const lastForced=new Array(N).fill(-1);
    for (let k=1,lf=-1;k<N;k++){ lastForced[k]=lf; if(bcs[k].kind==='penalty'&&bcs[k].penalty<=-10000) lf=k; }

    for (let j=1;j<N;j++) {
        const bcJ=bcs[j];
        if (!allowDisc&&bcJ.kind==='disc') continue;
        if (bcJ.penalty>=10000) continue;
        for (let i=0;i<j;i++) {
            if (i<lastForced[j]) continue;   // line would span a forced break
            for (let fc_i=0;fc_i<4;fc_i++) {
                const si=dp[i][fc_i]; if(!si) continue;
                const {w,s,z}=lineMetrics(bcs[i],bcJ,p);
                // A line carrying an infinite-order fill (\hfil from \\, \hfill)
                // absorbs positive slack instead of justifying: ratio 0, badness 0.
                const hasFill = bcJ.cumFill>bcs[i].cumFill;
                if (bcJ.kind==='end') {
                    const slack=lineWidthSp-w; if(slack<0&&(z===0||(-slack/z)>1)) continue;
                    const ratio=slack<0?slack/z:0, b=ratio<0?badness(-slack,z):0, lp=p.linePenalty+b;
                    let d=lp*lp;
                    // Last-line penalty: penalise if last line is shorter than lastLineMin
                    if (p.lastLineMin>0 && w<p.lastLineMin*lineWidthSp) d+=p.lastLinePenalty;
                    const fc_j=(ratio<0&&b>12)?3:2, td=si.demerits+d;
                    if(!dp[j][fc_j]||td<dp[j][fc_j].demerits) dp[j][fc_j]={demerits:td,prev_j:i,prev_fc:fc_i,ratio,hyphenated:false};
                    continue;
                }
                const slack=lineWidthSp-w;
                let ratio, b;
                if(hasFill&&slack>=0){ ratio=0; b=0; }   // fill absorbs the slack
                else{
                    if(slack>0) ratio=s>0?slack/s:Infinity; else if(slack<0) ratio=z>0?slack/z:-Infinity; else ratio=0;
                    if(ratio<-1) continue;
                    b=badness(Math.abs(slack),slack>=0?s:z);
                    if(b>threshold) { if(minRejectedBadness===null||b<minRejectedBadness) minRejectedBadness=b; continue; }
                }
                const fc_j=slack>=0?(b>99?0:b>12?1:2):(b>12?3:2);
                const lp=p.linePenalty+b; let d=Math.abs(lp)>=10000?100000000:lp*lp;
                if(bcJ.penalty>0) d+=bcJ.penalty*bcJ.penalty;
                else if(bcJ.penalty>-10000) d-=bcJ.penalty*bcJ.penalty;
                if(Math.abs(fc_j-fc_i)>1) d+=p.adjDemerits;
                if(bcJ.kind==='disc'&&si.hyphenated) d+=p.doubleHyphenDemerits;
                const td=si.demerits+d;
                if(!dp[j][fc_j]||td<dp[j][fc_j].demerits) dp[j][fc_j]={demerits:td,prev_j:i,prev_fc:fc_i,ratio,hyphenated:bcJ.kind==='disc'};
            }
        }
    }
    const endIdx=N-1; if(bcs[endIdx].kind!=='end') return {breaks:null,minRejectedBadness};
    let bestFc=-1, bestD=Infinity;
    for(let fc=0;fc<4;fc++) if(dp[endIdx][fc]&&dp[endIdx][fc].demerits<bestD){bestD=dp[endIdx][fc].demerits;bestFc=fc;}
    if(bestFc===-1) return {breaks:null,minRejectedBadness};
    const breaks=[]; let j=endIdx,fc=bestFc;
    while(j>0){breaks.push({bcIdx:j,fc,demerits:dp[j][fc].demerits,ratio:dp[j][fc].ratio});const pj=dp[j][fc].prev_j,pfc=dp[j][fc].prev_fc;j=pj;fc=pfc;}
    breaks.reverse(); return {breaks,minRejectedBadness};
}

function extractLineNodes(startBC, endBC, nodes) {
    const result=[]; let from;
    if(startBC.kind==='start'){from=0;}
    else{if(startBC.kind==='disc') for(const pn of nodes[startBC.nodeIdx].post) result.push(pn); from=startBC.nodeIdx+1;}
    // Glue and kern are discarded at a line break, but only at a *break*: at
    // the very start of a paragraph they are real content. \subparagraph* and
    // friends make this visible — \@xsect drops the usual \parindent box and
    // re-inserts the indent as \hskip\parindent glue, which stripping here
    // would delete from the render while the break candidates still counted
    // its width, leaving the first line short by exactly the indent.
    if(startBC.kind!=='start'&&result.length===0){while(from<endBC.nodeIdx&&(nodes[from].type==='glue'||nodes[from].type==='kern'))from++;}
    const to=endBC.nodeIdx;
    for(let i=from;i<to;i++) if(nodes[i].type!=='local_par') result.push(nodes[i]);
    if(endBC.kind==='disc') for(const pn of nodes[endBC.nodeIdx].pre) result.push(pn);
    return result;
}

function greedyFallback(bcs, nodes, lineWidthSp, p) {
    const breaks=[]; let s=0;
    for(let j=1;j<bcs.length;j++){
        const {w}=lineMetrics(bcs[s],bcs[j],p);
        if(bcs[j].kind==='end'){breaks.push({bcIdx:j,fc:2,demerits:0,ratio:0});break;}
        if(w>lineWidthSp&&j>s+1){breaks.push({bcIdx:j-1,fc:2,demerits:0,ratio:0});s=j-1;}
    }
    return breaks;
}

function kpBreak(bcs, nodes, lineWidthSp, p) {
    let breaks=null;
    if (p.pretolerance >= 0)
        breaks = kpPass(bcs,lineWidthSp,p.pretolerance,false,p).breaks;
    if(!breaks) breaks = kpPass(bcs,lineWidthSp,p.tolerance,true,p).breaks;
    if(!breaks) breaks = kpPass(bcs,lineWidthSp,p.tolerance2,true,p).breaks;
    if(!breaks) breaks = kpPass(bcs,lineWidthSp,p.emergencyTolerance,true,p).breaks;
    if(!breaks) breaks = greedyFallback(bcs,nodes,lineWidthSp,p);
    const lines=[];
    for(let k=0;k<breaks.length;k++){
        const startBC=k===0?bcs[0]:bcs[breaks[k-1].bcIdx], endBC=bcs[breaks[k].bcIdx];
        lines.push({nodes:extractLineNodes(startBC,endBC,nodes),ratio:breaks[k].ratio,fitness:breaks[k].fc,leftProtrusion:startBC.leftProtrusion});
    }
    return lines;
}

// ── Adaptive line spacing ─────────────────────────────────────────────────────

function lineProfile(fontInfo, nodes, xStart, ratio, expandRatio) {
    const items=[];
    function walk(ns, x, r, er) {
        for(const n of ns){
            switch(n.type){
                case 'glyph':{
                    const scale=er!==0?1+er:1, w=gW(n)*scale*SP_TO_PX;
                    const h=gH(n)*SP_TO_PX, d=gD(n)*SP_TO_PX;
                    items.push({x1:x,x2:x+w,h,d}); x+=w; break;
                }
                case 'glue':{let w=n.width; if(r>0&&!(n.stretch_order||0)&&n.stretch>0)w+=r*n.stretch; else if(r<0&&!(n.shrink_order||0)&&n.shrink>0)w+=r*n.shrink; x+=w*SP_TO_PX; break;}
                case 'kern': x+=kW(n)*(1+er)*SP_TO_PX; break;   // lax: fitted (see kW)
                case 'disc': x=walk(n.replace,x,0,er); break;
                case 'math': x+=n.surround*SP_TO_PX; break;
                case 'picture':{
                    // lax: the fitted box (see pictureFit), so the leading
                    // around a scaled-down picture follows its drawn height.
                    const w=pW(n)*SP_TO_PX;
                    items.push({x1:x,x2:x+w,h:pH(n)*SP_TO_PX,d:pD(n)*SP_TO_PX});
                    x+=w; break;
                }
                case 'hlist':case 'vlist':{
                    // lax: bW/bH/bD — the fitted box when it wraps a fitted picture.
                    const w=bW(n)*SP_TO_PX, shift=(n.shift??0)*SP_TO_PX;
                    items.push({x1:x,x2:x+w,h:Math.max(0,bH(n)*SP_TO_PX-shift),d:Math.max(0,bD(n)*SP_TO_PX+shift)});
                    x+=w; break;
                }
            }
        }
        return x;
    }
    walk(nodes,xStart,ratio,expandRatio);
    return items;
}

function minRequiredAdvance(upper, lower) {
    let req=0;
    for(const u of upper){if(u.d<=0)continue; for(const l of lower){if(l.h<=0)continue; if(u.x2>l.x1&&l.x2>u.x1) req=Math.max(req,u.d+l.h);}}
    return req;
}

// TeX's interline spacing rule, in px. Given the previous line's depth and this
// line's ascent, and the paragraph's \baselineskip / \lineskip / \lineskiplimit
// (all px), return the baseline-to-baseline advance TeX would use: normally the
// baselineskip, but when the two lines are tall enough that the baselineskip glue
// would fall below lineskiplimit, the fixed lineskip instead. This is exactly the
// rule LaTeX applies, so lines land at the LaTeX distance.
function texInterlineAdvance(prevDepth, thisAscent, m) {
    return (m.bskip - prevDepth - thisAscent >= m.lskiplimit)
        ? m.bskip
        : prevDepth + thisAscent + m.lskip;
}
// The glue portion of that advance (advance minus the two abutting extents), used
// when segments are stacked as boxes with a margin between them.
function texInterlineGlue(prevDepth, thisAscent, m) {
    return texInterlineAdvance(prevDepth, thisAscent, m) - prevDepth - thisAscent;
}

// ── Citations ──────────────────────────────────────────────────────────────────
// A \lrcite number carries its reference number on each of its digit glyphs
// (serializer `cite`). The renderer only *tags* those glyphs — class lr-cite and
// data-cite="<n>"; all behaviour lives in one shared popover driven by delegated
// document events. Delegation (rather than per-glyph listeners) means it does not
// matter when a glyph is painted, that a number is several separate <tspan>s, or
// whether SVG text elements reliably fire mouseenter — a single listener on the
// document handles every citation.
//
//   hover a number → preview it (popover anchored under the number, arrow to it)
//   click a number → pin it open, so its doi/url link is clickable
//   click again, click ×, or click away → close
//
// The reference is typeset from structured .bib fields (title / authors / rest /
// link) produced by scripts/build-citations.py.

let citeData = {};        // { "16": {title, authors, rest, link:{href,label}}, ... }
let citePop = null;       // shared popover element
let citeContent = null;   // its text container
let citeArrow = null;     // the little triangle pointing at the number
let pinnedNum = null;     // reference number of the pinned popover, or null
let pinnedAnchor = null;  // a glyph of the pinned number (to re-anchor on scroll)

function installCitations() {
    const raw = document.getElementById('lr-citations');
    if (raw) {
        try {
            let d = JSON.parse(raw.textContent);
            // Tolerate a doubly-encoded payload (JSON string of JSON).
            if (typeof d === 'string') d = JSON.parse(d);
            if (d && typeof d === 'object') citeData = d;
        } catch { /* leave citeData empty; citations simply stay inert */ }
    }
    // No citation data on the page → nothing for a popover to show. Don't build
    // the popover DOM at all, so a page that doesn't ship the citation CSS never
    // renders a stray close button (the popover relies on that CSS to stay hidden
    // until opened).
    if (Object.keys(citeData).length === 0) return;
    if (citePop) return;

    citePop = document.createElement('div');
    citePop.id = 'lr-cite-pop';
    citePop.setAttribute('role', 'tooltip');
    citeArrow = document.createElement('div'); citeArrow.className = 'lr-cite-arrow';
    const close = document.createElement('button');
    close.className = 'lr-cite-close'; close.type = 'button';
    close.setAttribute('aria-label', 'Close'); close.textContent = '×';
    citeContent = document.createElement('div'); citeContent.className = 'lr-cite-content';
    citePop.append(citeArrow, close, citeContent);
    document.body.appendChild(citePop);
    close.addEventListener('click', closeCite);

    const citeAt = t => (t && t.closest) ? t.closest('[data-cite]') : null;

    // Hover preview (only while nothing is pinned).
    document.addEventListener('pointerover', e => {
        if (pinnedNum !== null) return;
        const el = citeAt(e.target);
        if (el) openCite(el.dataset.cite, el, false);
    });
    document.addEventListener('pointerout', e => {
        if (pinnedNum !== null) return;
        const from = citeAt(e.target);
        if (!from) return;
        const to = citeAt(e.relatedTarget);       // moving between digits of the
        if (!to || to.dataset.cite !== from.dataset.cite) closeCite();  // same number stays open
    });
    // Click a number to pin/unpin; click outside a pinned popover to close it.
    document.addEventListener('click', e => {
        const el = citeAt(e.target);
        if (el) {
            e.preventDefault();
            const num = el.dataset.cite;
            if (pinnedNum === num) closeCite(); else openCite(num, el, true);
        } else if (pinnedNum !== null && !citePop.contains(e.target)) {
            closeCite();
        }
    });

    const reflow = () => { if (pinnedNum !== null && pinnedAnchor) positionCite(pinnedAnchor); };
    window.addEventListener('scroll', reflow, { passive: true });
    window.addEventListener('resize', reflow);
}

function fillCite(num) {
    const ref = citeData[num];
    if (!ref) return false;
    citeContent.textContent = '';
    const add = (cls, text) => {
        const d = document.createElement('div'); d.className = cls; d.textContent = text;
        citeContent.appendChild(d);
    };
    if (ref.title)   add('lr-cite-title', ref.title);
    if (ref.authors) add('lr-cite-authors', ref.authors);
    if (ref.rest)    add('lr-cite-rest', ref.rest);
    // The link is taken verbatim from the .bib's own url/doi field, so it is
    // exact — never scraped back out of rendered text.
    if (ref.link && ref.link.href) {
        const d = document.createElement('div'); d.className = 'lr-cite-link';
        const a = document.createElement('a');
        a.href = ref.link.href; a.textContent = ref.link.label || ref.link.href;
        a.target = '_blank'; a.rel = 'noopener noreferrer';
        d.appendChild(a); citeContent.appendChild(d);
    }
    return true;
}

// The on-screen box of a single glyph <tspan>. Neither getBoundingClientRect()
// nor getBBox() works: for an SVG <tspan> both return the box of the whole
// enclosing <text> run, which would anchor every citation to the centre of its
// line. But each glyph carries its own baseline position as x/y attributes, so
// build the box from those (width ~half an em, height from the font size — rough
// is fine, it only anchors a popover) and map it through getScreenCTM(), which
// folds in every ancestor transform and the SVG's own screen position.
function glyphScreenRect(el) {
    const svg = el.ownerSVGElement;
    const ctm = el.getScreenCTM && el.getScreenCTM();
    const x = parseFloat(el.getAttribute('x'));
    const y = parseFloat(el.getAttribute('y'));
    const fs = parseFloat(el.getAttribute('font-size'));
    if (!svg || !ctm || !svg.createSVGPoint || !isFinite(x) || !isFinite(y) || !isFinite(fs)) {
        return el.getBoundingClientRect();
    }
    // Glyph box in user units: from the baseline up by ~cap height and a hair
    // below it, half an em wide (numerals).
    const x0 = x, x1 = x + fs * 0.5, y0 = y - fs * 0.72, y1 = y + fs * 0.10;
    const pt = svg.createSVGPoint();
    let L = Infinity, T = Infinity, R = -Infinity, B = -Infinity;
    for (const [px, py] of [[x0, y0], [x1, y0], [x0, y1], [x1, y1]]) {
        pt.x = px; pt.y = py;
        const p = pt.matrixTransform(ctm);
        L = Math.min(L, p.x); R = Math.max(R, p.x); T = Math.min(T, p.y); B = Math.max(B, p.y);
    }
    return { left: L, top: T, right: R, bottom: B, width: R - L, height: B - T };
}

// A number is several adjacent digit <tspan>s sharing data-cite (bracket, comma
// and space glyphs have no cite and break the run). Union their boxes so the
// popover and its arrow anchor to the whole number, not one digit.
function citeGroupRect(el) {
    const num = el.dataset.cite;
    const same = e => e && e.dataset && e.dataset.cite === num;
    const kin = [el];
    for (let p = el.previousElementSibling; same(p); p = p.previousElementSibling) kin.push(p);
    for (let n = el.nextElementSibling;     same(n); n = n.nextElementSibling)     kin.push(n);
    let L = Infinity, T = Infinity, R = -Infinity, B = -Infinity;
    for (const k of kin) {
        const b = glyphScreenRect(k);
        if (!b) continue;
        L = Math.min(L, b.left); T = Math.min(T, b.top); R = Math.max(R, b.right); B = Math.max(B, b.bottom);
    }
    return isFinite(L) ? { left: L, top: T, right: R, bottom: B, width: R - L, height: B - T }
                       : el.getBoundingClientRect();
}

// Anchor the popover to the number in viewport coordinates (position:fixed), so
// no positioned/transformed ancestor can shift it. Placed below the number, or
// above when there is no room; the arrow always points back at the number.
function positionCite(anchor) {
    const r = citeGroupRect(anchor);
    const gap = 9, vw = document.documentElement.clientWidth, vh = window.innerHeight;
    const pw = citePop.offsetWidth, ph = citePop.offsetHeight;
    const cx = r.left + r.width / 2;

    const left = Math.max(8, Math.min(cx - pw / 2, vw - pw - 8));
    const above = (r.bottom + gap + ph > vh) && (r.top - gap - ph > 0);
    const top = above ? r.top - ph - gap : r.bottom + gap;

    citePop.classList.toggle('lr-above', above);
    citePop.style.left = left + 'px';
    citePop.style.top  = top + 'px';
    // Measure the arrow offset from the popover's *actual* rendered left, so it
    // stays on the number through viewport clamping and sub-pixel rounding.
    const box = citePop.getBoundingClientRect();
    citeArrow.style.left = Math.max(12, Math.min(box.width - 12, cx - box.left)) + 'px';
}

function openCite(num, anchor, pin) {
    if (!fillCite(num)) return;
    citePop.classList.toggle('lr-pinned', pin);
    citePop.classList.add('lr-open');
    positionCite(anchor);                 // measured after content is in place
    if (pin) { pinnedNum = num; pinnedAnchor = anchor; }
}

function closeCite() {
    pinnedNum = null; pinnedAnchor = null;
    citePop.classList.remove('lr-open', 'lr-pinned');
}

// Tag a \lrcite digit glyph; the delegated listeners in installCitations do the
// rest, so nothing here needs re-binding when the reconciler reuses the element.
function registerCiteSource(el, num) {
    el.classList.add('lr-cite');
    el.dataset.cite = num;
}

// Bibliography [n] labels still carry `citetarget`; keep marking them in the DOM
// (a cheap data attribute) so a "jump to entry" affordance can use them later.
function registerCiteTarget(el, num) { el.dataset.citeTarget = num; }

// ── SVG renderer ──────────────────────────────────────────────────────────────

function svgEl(tag, attrs) {
    const el=document.createElementNS('http://www.w3.org/2000/svg',tag);
    for(const [k,v] of Object.entries(attrs)) el.setAttribute(k,String(v));
    return el;
}

// renderNodes emits glyphs, spaces, and rules through a sink object. The sink
// reconciles against the SVG elements of the previous render instead of
// recreating them: every element is keyed by the identity of the node-list
// object it renders (node objects are decoded once per block and never
// change). Because lines are contiguous slices of one fixed node sequence,
// the global emission order is break-invariant — a reflow can move elements
// between lines and toggle conditional ones (disc pre/post vs replace,
// boundary spaces) on and off, but never reorder them. So reconciliation is
// a single forward merge: reused elements in place cost two attribute writes,
// out-of-place ones a single insertBefore, and toggled-off ones are detached
// (kept in the byNode cache for later reattachment, so after both paths of a
// disc have been seen once, reflows allocate nothing at all).

// ── Transforms ────────────────────────────────────────────────────────────────
// A `transform` node (\rotatebox and friends) carries a PDF matrix applied
// about the current point; see the serializer, which folds TeX's save/setmatrix/
// restore whatsits into it. Two conversions are needed to get to SVG:
//
//   * PDF's y axis points up, SVG's points down. The SVG matrix is the PDF one
//     conjugated by the flip diag(1,-1), which negates the off-diagonal terms:
//     [a b c d] becomes matrix(a, -b, -c, d). Skip this and rotations come out
//     mirrored — 90° turns the wrong way.
//   * The matrix acts about the reference point, not the origin, so it is
//     wrapped in translate(±ref).
function svgMatrixOf(n, x, y) {
    return { a: n.m_a ?? 1, b: -(n.m_b ?? 0), c: -(n.m_c ?? 0), d: n.m_d ?? 1, x, y };
}

// The affine (a,b,c,d,e,f) of a transform about its reference point, in the
// order SVG's matrix() takes: x' = a·x + c·y + e, y' = b·x + d·y + f.
function affineOf(t) {
    return [t.a, t.b, t.c, t.d,
            t.x - (t.a * t.x + t.c * t.y),
            t.y - (t.b * t.x + t.d * t.y)];
}

// m1 ∘ m2 — apply m2, then m1.
function affineMul(m1, m2) {
    if (!m1) return m2;
    if (!m2) return m1;
    const [a1,b1,c1,d1,e1,f1] = m1, [a2,b2,c2,d2,e2,f2] = m2;
    return [a1*a2 + c1*b2,       b1*a2 + d1*b2,
            a1*c2 + c1*d2,       b1*c2 + d1*d2,
            a1*e2 + c1*f2 + e1,  b1*e2 + d1*f2 + f1];
}

function reconcileSink(byNode, used, stats) {
    let textParent = null, auxParent = null, lastTspan = null, lastRect = null;
    const stack = [];

    function place(parent, last, el, isNew) {
        const expected = last ? last.nextSibling : parent.firstChild;
        if (el !== expected) {
            parent.insertBefore(el, expected);
            if (!isNew) stats.moved++;
        }
    }

    return {
        beginLine(textEl, auxEl) { textParent = textEl; auxParent = auxEl; lastTspan = null; lastRect = null; },
        // Rotated glyphs cannot go in the line's shared <text>: a tspan takes
        // no transform of its own (SVG 1.1), and x/y on a tspan would fight
        // the group's matrix anyway. So a transform gets its own <g> holding
        // its own <text>, and sits in the aux parent next to rules and
        // pictures. Nesting works because the parents are stacked.
        beginTransform(n, tf) {
            let g = byNode.get(n);
            const isNew = !g;
            if (isNew) {
                g = svgEl('g', {});
                const t = svgEl('text', {});
                t.style.cssText = 'font-weight:normal;font-style:normal';
                g.appendChild(t);
                byNode.set(n, g); stats.created++;
            } else { stats.repositioned++; }
            const [a,b,c,d,e,f] = affineOf(tf);
            g.setAttribute('transform', `matrix(${a} ${b} ${c} ${d} ${e} ${f})`);
            place(auxParent, lastRect, g, isNew);
            used.add(g); lastRect = g;
            stack.push({ textParent, auxParent, lastTspan, lastRect });
            textParent = g.firstChild; auxParent = g;
            lastTspan = null; lastRect = g.firstChild;
            used.add(g.firstChild);
        },
        endTransform() {
            const s = stack.pop();
            textParent = s.textParent; auxParent = s.auxParent;
            lastTspan = s.lastTspan; lastRect = s.lastRect;
        },
        glyph(n, x, y, fi) {
            // No loadable font for this glyph → draw its metric boxes instead of
            // an unshapeable character (see missing()).
            if (fi?.unresolved) { this.missing(n, x, y); return; }
            let el = byNode.get(n), isNew = !el;
            if (isNew) {
                el = svgEl('tspan', {x, y, 'font-family': fi?.family ?? 'serif', 'font-size': fi?.size_px ?? 12});
                el.textContent = String.fromCodePoint(n.char);
                // Inline style so it wins over the page's `fill: currentColor`
                // rule; uncoloured glyphs keep currentColor (dark-mode aware).
                // Coloured ones go through the theme substitution maps.
                if (n.color) el.style.fill = colorFill(n.color);
                // Citation wiring (see installCitations). A \lrcite number's
                // glyphs become a clickable/hoverable citation; a bibliography
                // [n] label's glyphs become the scroll anchor. Attached once,
                // at creation, so reflow (which reuses the element) keeps them.
                if (n.cite)       registerCiteSource(el, n.cite);
                if (n.citetarget) registerCiteTarget(el, n.citetarget);
                byNode.set(n, el); stats.created++;
            } else {
                el.setAttribute('x', x); el.setAttribute('y', y); stats.repositioned++;
            }
            place(textParent, lastTspan, el, isNew);
            used.add(el); lastTspan = el;
        },
        // A glyph whose font could not be loaded: draw its TeX metric boxes — the
        // advance width by the height above the baseline, and by the depth below —
        // as two outlined rects, so the missing ink's place and size are visible.
        missing(n, x, y) {
            let el = byNode.get(n), isNew = !el;
            const w = gW(n) * SP_TO_PX;
            const h = gH(n) * SP_TO_PX;                 // above the baseline
            const d = gD(n) * SP_TO_PX;                 // below the baseline
            const boxes = [];
            if (h > 0) boxes.push([x, y - h, w, h]);
            if (d > 0) boxes.push([x, y,     w, d]);
            if (isNew) {
                el = svgEl('g', { class: 'latex-missing-glyph' });
                for (const [bx, by, bw, bh] of boxes) {
                    const r = svgEl('rect', { x: bx, y: by, width: bw, height: bh });
                    r.style.fill = 'none';
                    r.style.stroke = 'var(--latex-color-ff0000, #cc0000)';
                    r.style.strokeWidth = '1';
                    r.style.opacity = '0.55';
                    el.appendChild(r);
                }
                byNode.set(n, el); stats.created++;
            } else {
                const rects = el.children;
                boxes.forEach(([bx, by, bw, bh], i) => {
                    rects[i].setAttribute('x', bx);     rects[i].setAttribute('y', by);
                    rects[i].setAttribute('width', bw); rects[i].setAttribute('height', bh);
                });
                stats.repositioned++;
            }
            place(auxParent, lastRect, el, isNew);
            used.add(el); lastRect = el;
        },
        space(n, x, y) {
            let el = byNode.get(n), isNew = !el;
            if (isNew) {
                el = svgEl('tspan', {x, y});
                el.textContent = ' ';
                byNode.set(n, el); stats.created++;
            } else {
                el.setAttribute('x', x); el.setAttribute('y', y); stats.repositioned++;
            }
            place(textParent, lastTspan, el, isNew);
            used.add(el); lastTspan = el;
        },
        rule(n, x, y, w, h) {
            let el = byNode.get(n), isNew = !el;
            if (isNew) {
                el = svgEl('rect', {x, y, width: w, height: h});
                // Always set the fill inline rather than leaving it to page
                // CSS: a blanket `rect { fill: currentColor }` would also hit
                // the shapes inside a tikzpicture and flatten their colours,
                // since CSS outranks the presentation attributes dvisvgm emits.
                el.style.fill = n.color ? colorFill(n.color)
                                        : 'var(--latex-color-000000, currentColor)';
                byNode.set(n, el); stats.created++;
            } else {
                el.setAttribute('x', x); el.setAttribute('y', y);
                el.setAttribute('width', w); el.setAttribute('height', h);
                stats.repositioned++;
            }
            place(auxParent, lastRect, el, isNew);
            used.add(el); lastRect = el;
        },
        // A precompiled tikzpicture. Its markup never changes, so reflowing is
        // only ever a new transform — the drawing itself is built once.
        picture(n, x, y) {
            let el = byNode.get(n), isNew = !el;
            const pic = n.pic;
            if (isNew) {
                // A drawing carries its own colours (already rewritten to
                // the theme's custom properties), unlike glyph ink which is
                // themed wholesale. The class marks that boundary for page CSS
                // and for anyone inspecting the DOM.
                el = svgEl('g', { class: 'latex-picture' });
                if (pic) el.innerHTML = pic.svg;
                // dvisvgm omits fill on black paths (SVG's initial fill is
                // black), so the theme's default text colour is supplied here
                // by inheritance rather than rewritten into every path.
                el.setAttribute('fill', 'var(--latex-color-000000, currentColor)');
                byNode.set(n, el); stats.created++;
            } else {
                stats.repositioned++;
            }
            // The source viewBox is in bp; scaling it to the node's TeX width
            // makes the drawing fill its box exactly, at any zoom. (lax: the
            // box is the fitted one — a picture wider than the column is
            // scaled down uniformly, aspect preserved; see pictureFit.)
            const s = pic && pic.vb_w ? (pW(n) * SP_TO_PX) / pic.vb_w : 1;
            el.setAttribute('transform',
                `translate(${x} ${y - pH(n) * SP_TO_PX}) scale(${s})`);
            place(auxParent, lastRect, el, isNew);
            used.add(el); lastRect = el;
        },
    };
}

// ── Leaders ───────────────────────────────────────────────────────────────────
// Leader glue carries a box that TeX repeats across the glue's set width rather
// than leaving it blank; \xrightarrow is an arrow tail, a \cleaders run of
// en-dashes, and an arrowhead. The set width is whatever the enclosing box's
// glue setting produced, so the copies are laid out here rather than baked in.
//
// Placement follows TeX82 §626-627: as many whole copies as fit, then
//   \cleaders — the remainder is split evenly at the two ends (centred);
//   \xleaders — the remainder is spread evenly into count+1 gaps;
//   \leaders / \gleaders — copies align to a grid on the *enclosing* box rather
//     than to this glue, which is not information the node carries, so they are
//     packed from the left. Nothing in this pipeline uses them today.
const GLUE_LEADERS = 100, GLUE_CLEADERS = 101, GLUE_XLEADERS = 102;

// The DOM reconciler is keyed by node identity, so every tiled copy needs its
// own node objects: drawing one leader box N times would look up the same
// element N times, move it, and leave a single copy at the last position. The
// clones are cached on the glue node and reused while the count holds, which
// keeps the elements — and the reconciler's work — stable across reflows.
function deepCloneNode(o){
    if(Array.isArray(o)) return o.map(deepCloneNode);
    if(o&&typeof o==='object'){
        const r={};
        for(const k of Object.keys(o)) r[k]=deepCloneNode(o[k]);
        return r;
    }
    return o;
}

function leaderCopies(n, count){
    if(!n._leaderCopies || n._leaderCopies.length!==count){
        n._leaderCopies=[];
        for(let i=0;i<count;i++) n._leaderCopies.push(deepCloneNode(n.leader));
    }
    return n._leaderCopies;
}

function renderLeaders(fontInfo, sink, n, x, baselineY, wSp){
    const L=n.leader;
    if(!L || wSp<=0) return;

    // A rule leader is not tiled: TeX simply runs the rule the whole length
    // (\hrulefill). Running dimensions inherit from the enclosing box, which is
    // not reachable here, so they fall back to the rule's own.
    if(L.type==='rule'){
        const h=(L.height===RUNNING_RULE?0:(L.height??0))*SP_TO_PX;
        const d=(L.depth ===RUNNING_RULE?0:(L.depth ??0))*SP_TO_PX;
        if(h+d>0) sink.rule(L, x, baselineY-h, wSp*SP_TO_PX, h+d);
        return;
    }

    const Lw=L.width??0;
    if(Lw<=0) return;                     // would tile forever
    const count=Math.floor(wSp/Lw);
    if(count<1) return;                   // not even one copy fits: TeX draws nothing

    const slack=wSp-count*Lw;
    let start, step=Lw;
    if(n.subtype===GLUE_XLEADERS){ const gap=slack/(count+1); start=gap; step=Lw+gap; }
    else if(n.subtype===GLUE_CLEADERS){ start=slack/2; }
    else { start=0; }                     // \leaders / \gleaders — see note above

    const copies=leaderCopies(n,count);
    for(let i=0;i<count;i++){
        renderNodes(fontInfo,sink,[copies[i]],x+(start+i*step)*SP_TO_PX,baselineY,0,0,0);
    }
}

// Stack a vlist's children top-to-bottom. refY is the vlist's reference baseline
// and vlistX its left edge; both are supplied by the caller (already resolving any
// shift for the context the vlist appears in). Split out of renderNodes so a vlist
// nested inside another vlist can reuse it — without this, a vlist child was
// dropped, which silently deleted the inner half of a stacked construction
// (double math accents, \substack, nested roots, …), leaving one piece too high.
function renderVlistBody(fontInfo, sink, n, vlistX, refY){
    const{ratio:vr,fillOrder:vfo}=vlistGlueRatio(n);
    const vlistW=n.width;
    let curY=refY-n.height*SP_TO_PX;
    for(const child of n.children){
        if(child.type==='kern'){curY+=child.kern*SP_TO_PX;}
        else if(child.type==='glue'){curY+=setGlue(child,vr,vfo)*SP_TO_PX;}
        else if(child.type==='rule'){
            const rw=(child.width===RUNNING_RULE?vlistW:rW(child))*SP_TO_PX;   // lax: fitted (see rW)
            const rh=(child.height+child.depth)*SP_TO_PX;
            sink.rule(child,vlistX,curY,rw,rh);
            curY+=rh;
        } else if(child.type==='hlist'){
            const cb=curY+child.height*SP_TO_PX;
            const{ratio:hr,fillOrder:hfo}=hlistGlueRatio(child);
            renderNodes(fontInfo,sink,child.children,vlistX+(child.shift??0)*SP_TO_PX,cb,hr,0,hfo,child.height,child.depth);
            curY+=(child.height+child.depth)*SP_TO_PX;
        } else if(child.type==='vlist'){
            // Inside a vlist a box's shift is horizontal; the child's own baseline
            // sits child.height below the current pen, then we advance past it.
            renderVlistBody(fontInfo,sink,child,vlistX+(child.shift??0)*SP_TO_PX,curY+child.height*SP_TO_PX);
            curY+=(child.height+child.depth)*SP_TO_PX;
        }
    }
}

// runH/runD (sp) are the enclosing box's height and depth. A rule with a running
// dimension (the RUNNING_RULE sentinel) inherits it — that is how a \vrule stretches
// to the exact height of the \hbox it sits in (e.g. the two side edges of the amsthm
// QED box). Without this the rule is dropped and only the top/bottom edges show.
function renderNodes(fontInfo, sink, nodes, x, baselineY, ratio, expandRatio, fillOrder, runH, runD) {
    ratio=ratio||0; expandRatio=expandRatio||0; fillOrder=fillOrder||0; runH=runH||0; runD=runD||0;
    for(const n of nodes){
        switch(n.type){
            case 'rule':{
                // In an hlist a rule is a vrule: its width is set, its height/depth
                // run to the enclosing box. Draw it, then advance the pen by its width.
                const w =(n.width ===RUNNING_RULE?0:rW(n));   // lax: fitted (see rW)
                const h =(n.height===RUNNING_RULE?runH:(n.height??0));
                const d =(n.depth ===RUNNING_RULE?runD:(n.depth ??0));
                const hp=h*SP_TO_PX, dp=d*SP_TO_PX;
                if(w>0&&hp+dp>0) sink.rule(n, x, baselineY-hp, w*SP_TO_PX, hp+dp);
                x+=w*SP_TO_PX; break;
            }
            case 'glyph':{
                const scale=expandRatio!==0?1+expandRatio:1;
                sink.glyph(n, x, baselineY, fontInfo[String(n.font)]);
                x+=gW(n)*scale*SP_TO_PX; break;
            }
            case 'glue':{
                let w=n.width;
                if(ratio>0&&(n.stretch_order||0)===fillOrder&&n.stretch>0) w+=ratio*n.stretch;
                else if(ratio<0&&(n.shrink_order||0)===fillOrder&&n.shrink>0) w+=ratio*n.shrink;
                if(n.leader) renderLeaders(fontInfo,sink,n,x,baselineY,w);
                if(n.subtype===13) sink.space(n, x, baselineY);
                x+=w*SP_TO_PX; break;
            }
            case 'kern':  x+=kW(n)*(1+expandRatio)*SP_TO_PX; break;   // lax: fitted (see kW)
            case 'picture':{
                // The picture fills its TeX box exactly; the box is what makes
                // it behave like any other box in text, math or an align row.
                // (lax: the fitted box, see pictureFit.)
                sink.picture(n, x, baselineY);
                x+=pW(n)*SP_TO_PX; break;
            }
            case 'transform':{
                // The matrix is drawing-only: TeX advanced the pen by the
                // untransformed content and sized the *enclosing* box to the
                // rotated bbox, so the children still advance x exactly as
                // they did before the serializer grouped them. (graphicx makes
                // the content box zero-width, so in practice this is 0.) The
                // ratio/fillOrder pass through for the same reason — these
                // were siblings in the parent list and their glue is set by
                // the parent's packing.
                sink.beginTransform(n, svgMatrixOf(n, x, baselineY));
                x=renderNodes(fontInfo,sink,n.children,x,baselineY,ratio,expandRatio,fillOrder,runH,runD);
                sink.endTransform();
                break;
            }
            case 'disc':  x=renderNodes(fontInfo,sink,n.replace,x,baselineY,0,expandRatio,0,runH,runD); break;
            // lax: a \laxmark whatsit — an exact stream position, zero-size,
            // never drawn. Sinks that record anchors declare `marker`; the
            // paint and ink-measurement sinks do not, and skip it.
            case 'mark':  if (sink.marker) sink.marker(n, x, baselineY); break;
            // lax: a footnote's reference point — the same shape, its own
            // sink method (the superscript glyph before it is ordinary ink).
            case 'fnref': if (sink.footnote) sink.footnote(n, x, baselineY); break;
            case 'math':  x+=n.surround*SP_TO_PX; break;
            case 'hlist':{
                const{ratio:hr,fillOrder:hfo}=hlistGlueRatio(n);
                renderNodes(fontInfo,sink,n.children,x,baselineY+(n.shift??0)*SP_TO_PX,hr,0,hfo,n.height,n.depth);
                x+=bW(n)*SP_TO_PX; break;   // lax: the fitted width when wrapping a fitted picture
            }
            case 'vlist':
                // A vlist encountered here sits in an hlist context, where a box's
                // shift is vertical (downward); renderVlistBody stacks its contents.
                renderVlistBody(fontInfo,sink,n,x,baselineY+(n.shift??0)*SP_TO_PX);
                x+=bW(n)*SP_TO_PX; break;
        }
    }
    return x;
}

// ── Document → SVG element ────────────────────────────────────────────────────
// A block is an ordered stream of paragraphs and displays (see latex.proto).
// The two are laid out very differently but stack identically, so both are
// reduced to the same "line" shape — {nodes, ratio, er, x0} — and the existing
// profiling, spacing, and reconciliation machinery then treats them alike:
//
//   paragraph → Knuth-Plass re-breaks it at the reader's width, many lines
//   display   → one line whose single node is TeX's finished box
//
// Displays are never re-broken or re-packed: TeX already set their glue at
// compile time, and replaying that verbatim is what keeps \hfill, \rlap,
// \mathclap and alignment tabskips faithful to the PDF (re-packing would
// silently activate glue TeX deliberately left slack). The only freedom taken
// is horizontal placement: the box is centred at the reader's width, or
// pinned to the left edge and allowed to overflow when it does not fit — the
// container scrolls in that case.
//
// Split into two phases so far-from-viewport blocks can be sized without being
// drawn: layoutDocument runs KP + line spacing and sets the svg's dimensions
// (storing the result in cache.layout); paintDocument materialises the most
// recent layout into glyph/rule elements via the reconciling sink.

// Older blocks carry no content stream; treat them as all-paragraphs.
function contentStream(doc) {
    if (doc.content && doc.content.length) return doc.content;
    return doc.paragraphs.map((_, i) => ({ kind: 'paragraph', para: i + 1 }));
}

// A block is split into segments rather than drawn as one SVG: runs of text
// share an SVG, but every display gets its own. A display keeps its compiled
// width, so it can be wider than the column — in one shared SVG that overflow
// would scroll the whole block, dragging text that fits perfectly out of view.
// Giving each display its own scroll container (as MathJax and KaTeX do) keeps
// the text still and lets only the maths pan.
//
// Segmentation depends solely on the content stream, never on width, so the
// segment list is stable across reflows and every element stays reusable.
const HL_ALIGNMENT = 4;   // hlist subtype: one row of an alignment

function segmentsOf(doc) {
    const segs = [];
    let text = null, gap = 0, pendingMarkers = [];
    for (const item of contentStream(doc)) {
        if (item.kind === 'vspace') { gap = item.amount * SP_TO_PX; continue; }
        // lax: a stream marker between flow items. It becomes a zero-size
        // anchor element sitting in flow in front of the next segment (or
        // after the last one), so it tracks reflowed positions with no
        // arithmetic. It also closes the current text run; the split is
        // spacing-neutral because a text→text join reproduces TeX's own
        // interline rule as an inter-segment margin (see layoutDocument).
        // A vertical-mode footnote reference (\thanks) is the same anchor
        // shape, keyed by the footnote's ordinal (see anchorKey).
        if (item.kind === 'marker' || item.kind === 'footnote_ref') {
            if (item.n) pendingMarkers.push(item.kind === 'marker'
                ? { side: item.side === 'e' ? 'e' : 'b', n: item.n }
                : { fn: true, n: item.n });
            text = null;
            continue;
        }
        if (item.kind === 'display') {
            // Consecutive alignment rows are the rows of one align/gather, and
            // must be laid out together: they share a single offset so their
            // & alignment survives, and they pan as one unit rather than each
            // row scrolling separately. A \[..\] display is always its own
            // segment. (lax: a marker between rows forces a new segment — the
            // anchor needs a slot between the elements.)
            const isAlign = item.box.subtype === HL_ALIGNMENT;
            const last    = segs[segs.length - 1];
            if (isAlign && last && last.kind === 'display' && last.isAlign && pendingMarkers.length === 0) {
                last.rows.push({ item, gap });
            } else {
                segs.push({ kind: 'display', isAlign, rows: [{ item, gap: 0 }], gapBefore: gap, markersBefore: pendingMarkers });
                pendingMarkers = [];
            }
            text = null; gap = 0;
            continue;
        }
        const para = doc.paragraphs[item.para - 1];
        if (!para) continue;
        // Consecutive paragraphs normally merge into one text segment and stack
        // with adaptive leading. An explicit vspace before this paragraph (from
        // \vspace, or a section heading's before/after skip) breaks that merge:
        // the paragraph starts a new segment whose gapBefore reproduces exactly
        // the space TeX asked for (segment boxes stack baseline-to-baseline).
        // lax: a footnote's paragraphs form a segment of their own, keyed by
        // the footnote (a page lifts the whole element out as a sidenote);
        // a footnote of several paragraphs stays one segment.
        const footnote = para.footnote || 0;
        if (!text || gap || pendingMarkers.length || (text.footnote || 0) !== footnote) {
            text = { kind: 'text', items: [], gapBefore: gap, markersBefore: pendingMarkers };
            if (footnote) text.footnote = footnote;
            pendingMarkers = [];
            segs.push(text);
        }
        text.items.push({ index: item.para, para });
        gap = 0;
    }
    // lax: the footnote rule — the rule-line display in front of the first
    // footnote segment (\footnoterule, set in vertical mode as its own
    // display) — so a page showing sidenotes can hide it with them.
    const firstFn = segs.findIndex(seg => seg.footnote);
    if (firstFn > 0) {
        const prev = segs[firstFn - 1];
        if (prev.kind === 'display' && prev.rows.length === 1 && loneRule(prev.rows[0].item.box)) prev.footnoteRule = true;
    }
    return { segs, trailingMarkers: pendingMarkers };
}

// lax: the identity an anchor element is pooled under across reflows — a
// mark's side, or a footnote reference (`fn`, one per footnote).
function anchorKey(m) {
    return m.fn ? `fn:${m.n}` : `${m.n}:${m.side}`;
}

// lax: whether a line's node list carries a marker anywhere — the cheap gate
// before the exact recording walk. Decoded nodes always have (possibly empty)
// child arrays (toObject arrays:true), so the recursion is safe.
function containsMark(nodes) {
    for (const n of nodes) {
        if (n.type === 'mark' || n.type === 'fnref') return true;
        if ((n.children && containsMark(n.children)) || (n.replace && containsMark(n.replace))
            || (n.pre && containsMark(n.pre)) || (n.post && containsMark(n.post))) return true;
    }
    return false;
}

// lax: a sink that records marker pen positions and draws nothing. Driving
// the real renderNodes keeps anchor x-coordinates exactly where the painted
// glyphs land — glue setting, expansion, protrusion and all.
function anchorSink(out) {
    const noop = () => {};
    return {
        beginLine: noop, beginTransform: noop, endTransform: noop,
        glyph: noop, missing: noop, space: noop, rule: noop, picture: noop,
        marker(n, x, y) { out.push({ side: n.side === 'e' ? 'e' : 'b', n: n.n, x, y }); },
        footnote(n, x, y) { if (n.n) out.push({ fn: true, n: n.n, x, y }); },
    };
}

// lax: the band a paragraph (or display) occupies at the reader's width.
//
// The serializer records the paragraph's \parshape band as {indent, width}
// — LaTeX's lists indent through \parshape, and so do quote, quotation and
// the abstract, which inset *both* sides ({left, hsize − left − right}). The
// record carries no hsize, so the right inset is not stated; it is recovered
// as hsize − indent − width, with hsize taken to be the widest band in the
// document (cache.hsizeSp, see layoutDocument): the body paragraphs, which
// have no \parshape and report {0, hsize}. Both indents are fixed
// typographic measures and are kept as such — the text narrows between
// them, as it does for the left one — except at a column too narrow to
// afford them, where they are scaled back together so at least half the
// column remains for the text.
function paraBand(para, widthSp, hsizeSp) {
    let indentSp = Math.max(0, para.indent || 0);
    const bandSp = para.width || 0;
    let rightSp  = (hsizeSp && bandSp) ? Math.max(0, hsizeSp - indentSp - bandSp) : 0;
    const total  = indentSp + rightSp;
    if (total > widthSp / 2) {
        const k = (widthSp / 2) / total;
        indentSp = Math.round(indentSp * k);
        rightSp  = Math.round(rightSp  * k);
    }
    return { indentSp, rightSp, availSp: Math.max(1, widthSp - indentSp - rightSp) };
}

// lax: the nodes a lone picture is made of — the picture itself and the
// boxes wrapping it — when the node holds exactly one picture and no other
// ink (graphicx sets an externalised drawing in an \hbox of its own size;
// a \centerline or \mbox adds another). Null when the node is anything
// else: a picture beside text in a box could not be scaled without the
// box's width, which is TeX's, going wrong.
function lonePicture(n) {
    if (n.type === 'picture') return [n];
    if (n.type !== 'hlist' && n.type !== 'vlist') return null;
    let found = null;
    for (const c of n.children || []) {
        if (c.type === 'glyph' || c.type === 'rule' || c.type === 'disc' || c.type === 'transform') return null;
        if (c.type === 'picture' || c.type === 'hlist' || c.type === 'vlist') {
            const inner = lonePicture(c);
            if (!inner || found) return null;
            found = inner;
        }
    }
    return found ? [n, ...found] : null;
}

// lax: the same shape for a rule — the rule itself and the boxes wrapping
// it, when the node holds exactly one rule of a set width and no other
// ink. \hrule width\hsize in an \rlap (the LIPIcs abstract rule) and the
// footnote rule are what this recognises; a rule with a running width is
// sized by its box and needs nothing.
function loneRule(n) {
    if (n.type === 'rule') return n.width !== RUNNING_RULE && n.width > 0 ? [n] : null;
    if (n.type !== 'hlist' && n.type !== 'vlist') return null;
    let found = null;
    for (const c of n.children || []) {
        if (c.type === 'glue' || c.type === 'kern' || c.type === 'penalty') continue;
        if (c.type === 'rule' || c.type === 'hlist' || c.type === 'vlist') {
            const inner = loneRule(c);
            if (!inner || found) return null;
            found = inner;
            continue;
        }
        return null;
    }
    return found ? [n, ...found] : null;
}

// lax: the units a paragraph's own pictures (and lone rules) form among
// its top-level nodes: the chain of nodes that scale together, the width
// the unit advances the pen by, and the width of its ink. The two differ
// for pgf's idiom — \hbox to 0pt{<picture>\hss}\kern<width> — where the
// box advances nothing and the kern that follows it carries the width; the
// kern joins the chain so it shrinks with the picture. An \rlap of a
// picture or rule advances nothing at all and only its ink is fitted.
function pictureUnits(nodes) {
    const units = [];
    for (let i = 0; i < nodes.length; i++) {
        const n = nodes[i];
        if (n.type !== 'picture' && n.type !== 'rule' && n.type !== 'hlist' && n.type !== 'vlist') continue;
        const chain = lonePicture(n) || loneRule(n);
        if (!chain) continue;
        const inkSp = chain[chain.length - 1].width;
        let advSp = n.width;
        const next = nodes[i + 1];
        if (advSp === 0 && next && next.type === 'kern' && next.kern > 0) {
            chain.push(next);
            advSp = next.kern;
            i++;
        }
        units.push({ chain, advSp, inkSp });
    }
    return units;
}

// lax: whether KP could break this paragraph anywhere (the candidates
// buildBreakCandidates would find besides its start and end).
function hasBreakOpportunity(nodes) {
    for (const n of nodes) {
        if (n.type === 'glue' && n.subtype === 15) return false;
        if (n.type === 'glue' && n.subtype === 13 && !(n.stretch_order > 0)) return true;
        if (n.type === 'disc' || (n.type === 'penalty' && n.penalty < 10000)) return true;
    }
    return false;
}

// lax: scale a paragraph's own pictures (its top-level picture nodes, or
// top-level boxes holding nothing but one — see pictureUnits) down to the
// band when they are wider than it, and return a key naming the scales
// applied — the break candidates sum node widths, so they are rebuilt
// whenever this key changes (see layoutTextSegment). The one scale goes on
// the picture and on every wrapper, so their widths, heights and depths
// shrink together.
//
// Two fits, the smaller wins. Each unit alone is never wider than the
// band. And a paragraph KP cannot break anywhere is one line whatever its
// width — a figure of several panels set side by side — so when its
// natural width exceeds the band, every unit takes the same scale, the
// one that brings the line to the band: the panels keep their relative
// placement, and the line then centres (or sits) in the column as any
// line that fits does. Glyphs in the line are not scaled; the units
// absorb the whole excess, as far as they can.
function fitPictures(nodes, availSp) {
    const units = pictureUnits(nodes);
    if (!units.length) return '';
    for (const u of units) {
        for (const m of u.chain) pictureFit.delete(m);
        u.scale = Math.min(u.inkSp > availSp ? availSp / u.inkSp : 1,
                           u.advSp > availSp ? availSp / u.advSp : 1);
    }
    if (!hasBreakOpportunity(nodes)) {
        let natSp = 0, unitSp = 0;
        for (const n of nodes) natSp += nodeWidthSp(n);   // at scale 1: the map was just cleared
        for (const u of units) unitSp += u.advSp;
        if (natSp > availSp && unitSp > 0) {
            const s = (availSp - (natSp - unitSp)) / unitSp;
            if (s > 0) for (const u of units) u.scale = Math.min(u.scale, s);
        }
    }
    let key = '';
    for (const u of units) {
        if (u.scale < 1) {
            for (const m of u.chain) pictureFit.set(m, u.scale);
            key += u.scale.toFixed(6) + ';';
        }
    }
    return key;
}

// Lay a text segment out: KP-break each paragraph at the reader's width and
// stack the lines with the adaptive collision-based leading.
function layoutTextSegment(fontInfo, seg, widthPt, p, cache) {
    const widthSp  = Math.round(widthPt * 65536);
    const columnPx = widthPt * ZOOM;
    const lines = [], lrp = [], meta = [];

    for (const { index, para } of seg.items) {
        // lax: the paragraph's band at this column (both indents, see
        // paraBand), decided before the break candidates because a picture
        // fitted to the band changes its width and so the cached candidates.
        const band = paraBand(para, widthSp, cache.hsizeSp);
        const fitKey = fitPictures(para.nodes, band.availSp);
        let entry = cache.bcs.get(index);
        if (!entry || entry.fitKey !== fitKey) {
            entry = { bcs: buildBreakCandidates(para.nodes), fitKey };
            cache.bcs.set(index, entry);
        }
        const bcs = entry.bcs;

        // Alignment is per paragraph: TeX's \centering/\raggedright/\raggedleft
        // set the paragraph's \leftskip/\rightskip, which the serializer reads and
        // records as para.align. A paragraph with none (the common case) inherits
        // the block's alignment (p.align, from --latex-align). This is what centres
        // a \maketitle title inside an otherwise justified document.
        const align   = para.align || p.align;
        const justify = align === 'justify';

        // TeX interline parameters for this paragraph (sp → px). bskip>0 marks
        // "use the LaTeX rule"; absent (old data) falls back to adaptive leading.
        const lineMeta = para.baselineskip ? {
            bskip:      para.baselineskip  * SP_TO_PX,
            lskip:      (para.lineskip || 0) * SP_TO_PX,
            lskiplimit: (para.lineskiplimit || 0) * SP_TO_PX,
        } : null;

        // A list item's indent is a fixed measure (\leftmargin), so it stays
        // put and the text column narrows around it. The item's label hangs a
        // fixed distance to the left of this offset, which is precisely why
        // the indent has to be applied — at x0=0 the label would sit at
        // negative x and be clipped away. (lax: the right indent — an
        // abstract's or a quote's — is kept the same way; see paraBand.)
        const indentSp = band.indentSp;
        const indentPx = indentSp * SP_TO_PX;
        const availSp  = band.availSp;
        const availPx  = availSp * SP_TO_PX;

        for (const ln of kpBreak(bcs, para.nodes, availSp, p)) {
            // For non-justified modes: allow glue shrink (ratio<0) but never stretch.
            // When the line must shrink, rendering and positioning are identical to justify.
            // The alignment offset only applies to lines whose natural width fits the column.
            const ratio = justify ? ln.ratio : Math.min(0, ln.ratio);
            const er    = p.useExpansion ? ratio * p.maxExpand : 0;
            const protX = -(p.useProtrusion ? ln.leftProtrusion * SP_TO_PX : 0);
            const natSp = sumWidthSp(ln.nodes);
            let x0, fillRatio = 0, fillOrder = 0;
            if (ratio < 0) {
                x0 = protX;  // squeezed to fit — same position as justified
            } else {
                const natPx = natSp * SP_TO_PX;
                switch (align) {
                    case 'right':  x0 = availPx - natPx; break;
                    case 'center': x0 = (availPx - natPx) / 2; break;
                    default:       x0 = protX; break;
                }
                // A line with an infinite fill and room to spare distributes the
                // slack into that fill (KP left it at ratio 0), flushing whatever
                // follows to the right margin. This is set-once at layout: the fill
                // stretch is a fixed measure, only the available width varies.
                const fi = fillInfo(ln.nodes);
                if (fi.order > 0 && fi.stretch > 0) {
                    const slackSp = availSp - natSp;
                    if (slackSp > 0) { fillRatio = slackSp / fi.stretch; fillOrder = fi.order; x0 = protX; }
                }
            }
            lines.push(ln);
            lrp.push({ ratio, er, x0: x0 + indentPx, fillRatio, fillOrder });
            meta.push(lineMeta);
        }
    }
    return { lines, lrp, meta, W: Math.ceil(columnPx) };
}

// Where a box's ink actually starts and ends, in the box's own coordinates.
//
// A display's width says nothing about where its ink is: \[..\] carries its
// centring in the box's shift, amsmath bakes an align* row's centring into
// leading glue (140pt of it, hidden behind a negative backup cell), and
// numbered equations use frozen kerns. All of that was computed for the
// compiled \displaywidth and is meaningless at the reader's width. Measuring
// the ink sidesteps every one of those cases without special-casing any.
//
// This drives the real renderNodes with a sink that records instead of
// drawing, so the measurement cannot drift from what actually gets painted.
function inkExtentOf(fontInfo, box) {
    let min = Infinity, max = -Infinity;
    // Transform-aware: under a rotation it is the box's *height* that spans x,
    // so the horizontal extent has to be taken from the mapped corners rather
    // than from the node's width. Hence the full box rather than just (x, w).
    let M = null;
    const stack = [];
    const note = (x, w, yTop, yBot) => {
        if (!M) {
            if (x < min) min = x;
            if (x + w > max) max = x + w;
            return;
        }
        const [a,b,c,d,e,f] = M;
        for (const [px, py] of [[x,yTop],[x+w,yTop],[x,yBot],[x+w,yBot]]) {
            const tx = a*px + c*py + e;
            if (tx < min) min = tx;
            if (tx > max) max = tx;
        }
    };
    renderNodes(fontInfo, {
        beginLine() {},
        beginTransform(n, tf) { stack.push(M); M = affineMul(M, affineOf(tf)); },
        endTransform()        { M = stack.pop(); },
        glyph(n, x, y) { note(x, gW(n) * SP_TO_PX, y - gH(n) * SP_TO_PX, y + gD(n) * SP_TO_PX); },
        space()        {},                    // inter-word glue is not ink
        rule(n, x, y, w, h) { note(x, w, y, y + h); },
        picture(n, x, y) { note(x, pW(n) * SP_TO_PX, y - pH(n) * SP_TO_PX, y + pD(n) * SP_TO_PX); },
    }, [box], 0, 0, 0, 0, 0);
    return isFinite(min) ? { min, max } : { min: 0, max: 0 };
}

// A numbered display equation is packed by TeX to the full \displaywidth as
// [kern, body(#6), kern, number(#7)]: the equation centred in the band and its
// number flushed to the right margin. Because the whole thing is one rigid box,
// the re-centring below would count the number as ink and shove the equation
// left of centre. LuaTeX marks the number box with hlist subtype 7
// (equationnumber), so it can be lifted out exactly rather than guessed at.
// Returns the body (a shallow copy of the box with the number and its gap kern
// removed, its width shrunk to what remains) and the number box, or null.
//
// lax: two more shapes are recognised. \leqno puts the subtype-7 box first.
// And amsmath's alignments (align, gather, eqnarray too) do not use \eqno
// at all: the tag rides in the row's last cell (hlist subtype 5), a
// zero-width box holding an \llap of the tag, after the tabskip glue that
// centres the columns. That cell is lifted out the same way when it holds
// ink (an unnumbered row's tag cell is empty and stays put). The body's
// width is the *set* width of what remains, under the row's own glue
// setting, so the pen lands after the body exactly where the number is then
// placed relative to it.
const HL_EQNUMBER = 7;
const HL_CELL     = 5;   // hlist subtype: one cell of an alignment row
function splitEquationNumber(fontInfo, box) {
    const ch = box.children;
    if (!ch || ch.length < 2) return null;
    const isEqno = n => n.type === 'hlist' && n.subtype === HL_EQNUMBER;
    const isGap  = n => n.type === 'kern' || n.type === 'glue';
    let side = null, numberBox = null, from = 0, to = ch.length;
    if (isEqno(ch[ch.length - 1])) {
        side = 'right'; numberBox = ch[ch.length - 1]; to = ch.length - 1;   // drop the number…
        if (to > 0 && isGap(ch[to - 1])) to--;                               // …and its gap
    } else if (isEqno(ch[0])) {
        side = 'left'; numberBox = ch[0]; from = 1;
        if (from < to && isGap(ch[from])) from++;
    } else if (box.subtype === HL_ALIGNMENT) {
        let k = ch.length - 1;
        while (k > 0 && ch[k].type === 'glue') k--;                          // the closing tabskip
        const cell = ch[k];
        if (k > 0 && cell.type === 'hlist' && cell.subtype === HL_CELL && !cell.width
            && cell.children && cell.children.length) {
            side = 'right'; numberBox = cell; to = k;
        }
    }
    if (!numberBox) return null;
    const numInk = inkExtentOf(fontInfo, numberBox);
    if (!(numInk.max > numInk.min)) return null;                             // an empty tag cell
    const children = ch.slice(from, to);
    // The advance after the body must reflect only what is left, not the original
    // full-width box, or the trailing spacer/number would land a whole band away.
    const { ratio, fillOrder } = hlistGlueRatio(box);
    let width = 0;
    for (const n of children) width += n.type === 'glue' ? setGlue(n, ratio, fillOrder) : nodeWidthSp(n);
    const bodyBox = { ...box, children, width };
    return { bodyBox, numberBox, numInk, side };
}

// lax: the clearance amsmath keeps between an equation and its number before
// moving the number to a line of its own (1em of the body face), and the
// \jot-sized gap between the equation and that line.
const EQN_GAP_PX      = 10 * ZOOM;
const TAG_LINE_GAP_PX = 3 * ZOOM;

// Lay a display segment out: rigid boxes, never re-broken or re-packed. The
// only freedom taken is where the group as a whole sits horizontally.
//
// lax: a row's equation number is lifted out first (splitEquationNumber),
// so the group is centred on the *bodies'* ink and the numbers are placed
// afterwards, the way amsmath does: flush with the column's right (or, for
// \leqno, left) edge, on the equation's own baseline when the centred body
// leaves it room, else on a line of its own below (above for \leqno). The
// number is therefore always in view: a body wider than the column pans in
// the scroll box, whose width counts the bodies alone, while the number
// line sits at the column edge where no scrolling is needed to see it.
function layoutDisplaySegment(fontInfo, seg, widthPt, cache) {
    const columnPx = widthPt * ZOOM;
    const first    = seg.rows[0].item;
    // The band the display sits in: TeX's \displayindent and \displaywidth,
    // with the right inset recovered the same way a paragraph's is.
    const band   = paraBand({ indent: first.display_indent || 0, width: first.display_width || 0 },
                            Math.round(widthPt * 65536), cache && cache.hsizeSp);
    const diPx   = band.indentSp * SP_TO_PX;
    const availW = band.availSp * SP_TO_PX;

    // lax: a rule line — a display whose box holds one rule and nothing
    // else (a vertical-mode \hrule: the footnote separator, a class's
    // decorative rules). It is drawn at the column, never wider: a rule as
    // wide as its band (a running \hrule) spans the whole column, a shorter
    // one keeps its share of the band, flush left as TeX set it. The chain
    // takes the scale (see rW; the thickness is never scaled), and no
    // scroll box is ever needed for it.
    const ruleChain = seg.rows.length === 1 ? loneRule(first.box) : null;
    if (ruleChain) {
        const rule    = ruleChain[ruleChain.length - 1];
        const bandSp  = first.display_width || 0;
        const wantSp  = bandSp > 0 && rule.width < bandSp
            ? band.availSp * rule.width / bandSp
            : band.availSp;
        const s = Math.min(wantSp, band.availSp) / rule.width;
        for (const m of ruleChain) pictureFit.set(m, s);
        return {
            lines: [{ nodes: [first.box], ratio: 0, fitness: 2, leftProtrusion: 0 }],
            lrp:   [{ ratio: 0, er: 0, x0: diPx }],
            gaps:  [null],
            W: Math.ceil(columnPx),
        };
    }

    const rows = seg.rows.map(r => {
        const split = splitEquationNumber(fontInfo, r.item.box);
        const body  = split ? split.bodyBox : r.item.box;
        return {
            ...r,
            // TeX's placement of this row within its band, kept verbatim.
            shiftPx: ((r.item.display_shift || 0) - (r.item.display_indent || 0)) * SP_TO_PX,
            body,
            ink: inkExtentOf(fontInfo, body),
            num: split,
        };
    });

    // One offset for the whole group: rows keep their relative positions, so
    // an alignment's & columns stay aligned no matter where the group lands.
    let gMin = Infinity, gMax = -Infinity;
    for (const r of rows) {
        gMin = Math.min(gMin, r.shiftPx + r.ink.min);
        gMax = Math.max(gMax, r.shiftPx + r.ink.max);
    }
    const groupW = gMax - gMin;
    // Centre the ink when it fits; otherwise pin its left edge to x=0 so none
    // of it ends up at negative x, where scrolling could never reach it.
    const offset = groupW <= availW
        ? diPx + (availW - groupW) / 2 - gMin
        : -gMin;

    const lines = [], lrp = [], gaps = [];
    const push = (nodes, x0, gap, tag) => {
        // tag: a line holding only an equation number, at the column edge
        // where no scrolling is needed — the scroll cue keeps clear of it.
        lines.push({ nodes, ratio: 0, fitness: 2, leftProtrusion: 0, tag: !!tag });
        lrp.push({ ratio: 0, er: 0, x0 });
        gaps.push(gap);
    };
    rows.forEach((r, j) => {
        const x0     = offset + r.shiftPx;
        const rowGap = j === 0 ? null : (r.gap || null);
        if (!r.num) { push([r.body], x0, rowGap); return; }
        const { numberBox, numInk, side } = r.num;
        const bodyAdv = x0 + r.body.width * SP_TO_PX;          // the pen after the body
        if (side === 'right') {
            const xNum = diPx + availW - numInk.max;             // number ink flush right
            if (x0 + r.ink.max + EQN_GAP_PX <= xNum + numInk.min) {
                push([r.body, { type: 'kern', kern: (xNum - bodyAdv) / SP_TO_PX }, numberBox], x0, rowGap);
            } else {
                push([r.body], x0, rowGap);
                push([numberBox], xNum, TAG_LINE_GAP_PX, true);
            }
        } else {
            const xNum = diPx - numInk.min;                      // number ink flush left
            if (xNum + numInk.max + EQN_GAP_PX <= x0 + r.ink.min) {
                const numAdv = xNum + numberBox.width * SP_TO_PX;
                push([numberBox, { type: 'kern', kern: (x0 - numAdv) / SP_TO_PX }, r.body], xNum, rowGap);
            } else {
                push([numberBox], xNum, rowGap, true);
                push([r.body], x0, TAG_LINE_GAP_PX);
            }
        }
    });

    return {
        lines, lrp, gaps,
        // Only this segment may grow past the column, and only as far as the
        // ink truly reaches — so a short display never scrolls.
        W: Math.ceil(Math.max(columnPx, offset + gMax)),
    };
}

function layoutDocument(fontInfo, doc, widthPt, p, cache) {
    // Point the glyph-metrics reader at this document's table, and stash it on the
    // cache so paintDocument (which is handed only the cache) reads the same one.
    // fontInfo is stashed too, so the IntersectionObserver — which is handed only a
    // segment reference — can repaint it (see observeSegments / segIO).
    useGlyphMetrics(doc.glyph_metrics);
    cache.metrics = doc.glyph_metrics;
    cache.fontInfo = fontInfo;
    const columnPx = widthPt * ZOOM;
    const minGapPx = p.minGapPt * ZOOM;
    const padPx    = p.padPt    * ZOOM;

    // Break candidates depend only on the node list, never on width or params,
    // so they are cached per paragraph across every reflow. (lax: except
    // through a fitted picture's width — each entry carries the fit key it
    // was built under; see layoutTextSegment.)
    cache.bcs = cache.bcs || new Map();
    // lax: the document's \hsize, recovered as the widest paragraph band in
    // the content stream (see paraBand). Computed once per block.
    if (cache.hsizeSp === undefined) {
        let h = 0;
        for (const it of contentStream(doc)) {
            const para = it.para ? doc.paragraphs[it.para - 1] : null;
            if (para) h = Math.max(h, (para.indent || 0) + (para.width || 0));
        }
        cache.hsizeSp = h;
    }
    const { segs, trailingMarkers } = segmentsOf(doc);

    if (!cache.dom) {
        const root = document.createElement('div');
        // lax: paragraph-marker anchors are positioned absolutely in the
        // block's own coordinate space (see placeAnchors).
        root.style.position = 'relative';
        cache.dom = { root, segs: [], byNode: new Map(), live: new Set(), anchors: new Map() };
    }
    const dom = cache.dom;
    dom.root.style.visibility = '';   // may have been hidden while paint was deferred

    const laid = segs.map((seg, i) => {
        // lax: a footnote segment takes the sidenote measure when the page
        // has set one (params.footnoteWidthPt, see footnoteWidthFromEl).
        const geom = seg.kind === 'display'
            ? layoutDisplaySegment(fontInfo, seg, widthPt, cache)
            : layoutTextSegment(fontInfo, seg, seg.footnote && p.footnoteWidthPt ? p.footnoteWidthPt : widthPt, p, cache);

        // Profiles use actual render coords so collision detection matches real ink positions.
        const profiles = geom.lines.map((ln, j) =>
            lineProfile(fontInfo, ln.nodes, geom.lrp[j].x0, geom.lrp[j].ratio, geom.lrp[j].er)
        );
        const ascent     = (profiles[0] ?? []).reduce((m, it) => Math.max(m, it.h), 0);
        const baselineYs = [ascent];
        for (let j = 1; j < geom.lines.length; j++) {
            const gap = geom.gaps && geom.gaps[j];
            let advance;
            if (gap) {
                // TeX's own spacing between the rows of an alignment. Measured
                // baseline-to-baseline it must clear the previous depth and
                // this row's ascent.
                const prevDepth = profiles[j-1].reduce((m, it) => Math.max(m, it.d), 0);
                const rowAscent = profiles[j].reduce((m, it) => Math.max(m, it.h), 0);
                advance = prevDepth + gap + rowAscent;
            } else {
                const prevDepth = profiles[j-1].reduce((m, it) => Math.max(m, it.d), 0);
                const thisAsc   = profiles[j].reduce((m, it) => Math.max(m, it.h), 0);
                const lm = geom.meta && geom.meta[j];
                if (lm) {
                    // Land the line at exactly the LaTeX baseline-to-baseline.
                    advance = texInterlineAdvance(prevDepth, thisAsc, lm);
                } else {
                    // No captured metrics (older data): adaptive collision leading.
                    const needed = minRequiredAdvance(profiles[j-1], profiles[j]);
                    advance = needed > minGapPx ? needed + padPx : minGapPx;
                }
            }
            baselineYs.push(baselineYs[j-1] + advance);
        }
        const firstAscent = ascent;
        const lastDepth = (profiles[profiles.length-1] ?? []).reduce((m, it) => Math.max(m, it.d), 0);
        const H = baselineYs[baselineYs.length-1] + lastDepth;

        // lax: exact positions for in-paragraph markers, recorded by driving
        // the real renderer over each marker-bearing line — they land where
        // paint would put them, at this width, and are re-recorded on every
        // reflow. Coordinates are the segment svg's own (x, baselineY).
        const anchors = [];
        for (let j = 0; j < geom.lines.length; j++) {
            if (!containsMark(geom.lines[j].nodes)) continue;
            const { ratio, er, x0, fillRatio, fillOrder } = geom.lrp[j];
            renderNodes(fontInfo, anchorSink(anchors), geom.lines[j].nodes, x0, baselineYs[j],
                        fillOrder ? fillRatio : ratio, er, fillOrder || 0);
        }

        // A segment's box spans its first ascent to its last depth, so stacking
        // segments with margin-top = gap reproduces exactly the baseline-to-
        // baseline advance TeX asked for. firstMeta carries this segment's leading
        // parameters so a text→text join can add TeX's interline glue (see below).
        // lax: the bands a lone equation-number line occupies at the top
        // (\leqno) or bottom of a display, in px from the svg's edges; the
        // scroll cue's fades are inset past them (paintSegment).
        const n = geom.lines.length;
        const tagTop    = n > 1 && geom.lines[0].tag
            ? baselineYs[1] - profiles[1].reduce((m, it) => Math.max(m, it.h), 0) : 0;
        const tagBottom = n > 1 && geom.lines[n-1].tag
            ? H - (baselineYs[n-2] + profiles[n-2].reduce((m, it) => Math.max(m, it.d), 0)) : 0;
        return { ...geom, seg, profiles, baselineYs, H, firstAscent, lastDepth, anchors, tagTop, tagBottom,
                 firstMeta: (geom.meta && geom.meta[0]) || null, gapBefore: seg.gapBefore || 0 };
    });

    // lax: anchor elements, pooled by mark identity so reflows re-place the
    // same element (deep links and card joins keep their targets). The begin
    // side carries the page-wide id the cross-links use.
    // (lax: a footnote reference is pooled the same way, under its own
    // class and id — fn-ref-<k> — so a page can join a sidenote to it.)
    const anchorEl = (m) => {
        const key = anchorKey(m);
        let a = dom.anchors.get(key);
        if (!a) {
            a = document.createElement('span');
            if (m.fn) {
                a.className = 'latex-anchor latex-fnref';
                a.dataset.footnote = String(m.n);
                a.id = `fn-ref-${m.n}`;
            } else {
                a.className = 'latex-anchor';
                a.dataset.mark = String(m.n);
                a.dataset.side = m.side;
                if (m.side === 'b') a.id = `m${m.n}`;
            }
            dom.anchors.set(key, a);
        }
        return a;
    };

    // The per-segment elements persist across renders; only contents reconcile.
    while (dom.segs.length < laid.length) {
        // xmlns:xlink is declared so a picture's `<use xlink:href=…>` (dvisvgm
        // emits the xlink form) resolves once its markup is injected via innerHTML.
        const svg = svgEl('svg', { xmlns:'http://www.w3.org/2000/svg', 'xmlns:xlink':'http://www.w3.org/1999/xlink' });
        // Block CSS cascade from prose containers; SVG text uses explicit per-glyph font families.
        svg.style.cssText = 'display:block;overflow:visible;font-weight:normal;font-style:normal';
        dom.segs.push({ svg, wrap: null, pairs: [] });
    }
    dom.root.replaceChildren();
    laid.forEach((L, i) => {
        const s = dom.segs[i];
        s.svg.setAttribute('width', L.W);
        s.svg.setAttribute('height', L.H);
        s.svg.setAttribute('viewBox', `0 0 ${L.W} ${L.H}`);

        // Only a display that genuinely overflows gets a scroll box, because a
        // scroll box is also a *clipping* box: CSS forces overflow-y to 'auto'
        // once overflow-x is set, and there is no way to scroll one axis while
        // letting the other bleed. Ink that legitimately hangs outside its box
        // — accents, protrusion, delimiter overshoot — would be cut off. So a
        // display that fits is mounted bare and can bleed freely; only one that
        // must pan pays for it, and its wrapper is padded to spare the bleed.
        const overflows = L.seg.kind === 'display' && L.W > columnPx;
        let mount = s.svg;
        if (overflows) {
            // lax: the scroll box sits in a frame that carries the cue that
            // there is more to the side — data-scroll names the edge(s) the
            // box can still scroll toward, and the page's stylesheet fades
            // those edges (.latex-display-frame). Kept current on scroll.
            if (!s.wrap) {
                s.wrap  = document.createElement('div');
                s.frame = document.createElement('div');
                s.frame.className = 'latex-display-frame';
                s.frame.appendChild(s.wrap);
                s.wrap.addEventListener('scroll', () => noteScrollEdges(s), { passive: true });
            }
            s.wrap.className = 'latex-display';
            if (s.svg.parentNode !== s.wrap) s.wrap.replaceChildren(s.svg);
            mount = s.frame;
        } else if (s.wrap && s.svg.parentNode === s.wrap) {
            s.svg.remove();          // no longer overflowing: shed the scroll box
        }
        // Between two text segments TeX inserts interline (baselineskip) glue on
        // top of any explicit \vspace, exactly as it does between the lines of a
        // paragraph. Reproduce it so a heading sits the LaTeX distance above its
        // body — and independently of the heading's descender depth, since the
        // glue absorbs that. Displays keep their own captured spacing.
        const prev = laid[i-1];
        let margin = L.gapBefore || 0;
        if (i > 0 && L.seg.kind === 'text' && prev.seg.kind === 'text' && L.firstMeta) {
            margin += texInterlineGlue(prev.lastDepth, L.firstAscent, L.firstMeta);
        }
        s.svg.style.marginTop = '';
        if (s.frame) s.frame.style.marginTop = '';
        mount.style.marginTop = margin ? `${margin}px` : '';
        // lax: a footnote's segment and the rule in front of the first one
        // are named for the page (segmentation is width-independent, so a
        // segment's element keeps its role across reflows).
        if (L.seg.footnote) {
            mount.classList.add('latex-footnote');
            mount.dataset.footnote = String(L.seg.footnote);
        }
        if (L.seg.footnoteRule) mount.classList.add('latex-footnote-rule');
        // lax: stream-marker anchors sit in flow between the mounts. They are
        // zero-size and margin-free, so the next mount's collapsed margin is
        // exactly what it was without them.
        for (const m of (L.seg.markersBefore || [])) {
            const a = anchorEl(m);
            a.style.position = '';
            a.style.left = '';
            a.style.top = '';
            dom.root.appendChild(a);
        }
        dom.root.appendChild(mount);
    });
    // lax: markers after the last flow item, and the absolutely positioned
    // elements for in-paragraph markers. Their coordinates need the block in
    // the document, so placeAnchors (called after the root is mounted, and
    // after every reflow) fills them in.
    for (const m of trailingMarkers) {
        const a = anchorEl(m);
        a.style.position = '';
        a.style.left = '';
        a.style.top = '';
        dom.root.appendChild(a);
    }
    for (const L of laid) {
        for (const m of (L.anchors || [])) dom.root.appendChild(anchorEl(m));
    }
    // lax: the scroll cues need the boxes' final widths — read once the
    // root is in the document (initBlock mounts it after this returns).
    requestAnimationFrame(() => { for (const s of dom.segs) if (s.frame && s.frame.parentNode) noteScrollEdges(s); });

    cache.layout = { laid };
    // Track each segment by its own <svg>, not by a running height model that would
    // drift from the real layout (see the per-segment painting section).
    observeSegments(cache);
    return dom.root;
}

// lax: which edge(s) a display's scroll box can still scroll toward —
// 'start' (only to the right), 'end' (only back to the left), 'both', or
// 'none' when it fits after all. Stamped on the frame for the stylesheet.
function noteScrollEdges(s) {
    const w = s.wrap, max = w.scrollWidth - w.clientWidth;
    const state = max <= 1 ? 'none' : w.scrollLeft <= 1 ? 'start' : w.scrollLeft >= max - 1 ? 'end' : 'both';
    if (s.frame.dataset.scroll !== state) s.frame.dataset.scroll = state;
}

// lax: pin each in-paragraph anchor at its recorded (x, baselineY), mapped
// from the segment svg's space into the block root's. Rect reads rather than
// offsetTop: SVG elements have no offsetTop, and the rect difference is exact
// under margins and scroll wrappers alike. Called once the root is in the
// document — after the first mount and after every re-layout — so the reads
// are of real positions; stream anchors need nothing (they sit in flow).
function placeAnchors(cache) {
    const dom = cache.dom;
    if (!dom || !cache.layout || !dom.anchors || dom.anchors.size === 0) return;
    const rootBox = dom.root.getBoundingClientRect();
    cache.layout.laid.forEach((L, i) => {
        if (!L.anchors || !L.anchors.length) return;
        const svgBox = dom.segs[i].svg.getBoundingClientRect();
        for (const m of L.anchors) {
            const a = dom.anchors.get(anchorKey(m));
            if (!a) continue;
            a.style.position = 'absolute';
            a.style.left = `${svgBox.left - rootBox.left + m.x}px`;
            a.style.top = `${svgBox.top - rootBox.top + m.y}px`;
        }
    });
}

// Paint one segment: reconcile its lines' glyphs into its own <svg>. The reconcile
// is scoped to this segment (its own `live` set) because a node always lands in
// exactly one segment — segmentation is width-independent — so segments can be
// painted independently. That independence is what makes per-segment painting
// possible (see observeSegments / paintVisibleNow): a long document only pays the
// DOM cost for the segments that have been on screen, not for all of them at once.
function paintSegment(fontInfo, cache, i) {
    useGlyphMetrics(cache.metrics);   // a paint may run after another block laid out
    const dom = cache.dom;
    const L   = cache.layout.laid[i];
    const s   = dom.segs[i];
    const stats = cache.stats || (cache.stats = { created: 0, moved: 0, repositioned: 0, removed: 0 });
    const used  = new Set();
    const sink  = reconcileSink(dom.byNode, used, stats);

    // Grow/shrink the pool of per-line group pairs. Detached pairs are kept for
    // later regrowth; their stale children are swept by the live set.
    while (s.pairs.length < L.lines.length) {
        const g = svgEl('g', {'aria-hidden':'true', style:'user-select:none;pointer-events:none'});
        const text = svgEl('text', {});
        text.style.cssText = 'font-weight:normal;font-style:normal';
        s.pairs.push({ g, text, attached: false });
    }
    for (let j = 0; j < s.pairs.length; j++) {
        const pair = s.pairs[j];
        if (j < L.lines.length && !pair.attached) {
            s.svg.appendChild(pair.g);
            s.svg.appendChild(pair.text);
            pair.attached = true;
        } else if (j >= L.lines.length && pair.attached) {
            pair.g.remove();
            pair.text.remove();
            pair.attached = false;
        }
    }

    for (let j = 0; j < L.lines.length; j++) {
        const { ratio, er, x0, fillRatio, fillOrder } = L.lrp[j];
        sink.beginLine(s.pairs[j].text, s.pairs[j].g);
        // On a fill line finite glue is already at natural width (ratio 0), so the
        // single ratio slot carries the fill ratio and fillOrder selects the fill.
        renderNodes(fontInfo, sink, L.lines[j].nodes, x0, L.baselineYs[j],
                    fillOrder ? fillRatio : ratio, er, fillOrder || 0);
    }

    // Detach this segment's elements no longer rendered (disc paths toggled off,
    // spaces consumed by new break points). They stay cached in byNode.
    if (s.live) for (const el of s.live) if (!used.has(el)) { el.remove(); stats.removed++; }
    s.live = used;
    s.painted = true;
    s.dirty = false;

    // A display in a scroll box pays a price: overflow-x:auto forces overflow-y to
    // auto as well, so ink hanging above/below the nominal box (accents, deep
    // subscripts, delimiter overshoot) is clipped. Measure the painted ink (getBBox
    // is 1:1 since the viewBox matches width/height) and pad the wrapper by exactly
    // the vertical overshoot, so the display shows in full and still pans.
    if (s.wrap && s.svg.parentNode === s.wrap) {
        let bb;
        try { bb = s.svg.getBBox(); } catch { bb = null; }
        if (bb) {
            const BASE_PAD = 4, pad = v => Math.round(Math.max(0, v) + BASE_PAD) + 'px';
            s.wrap.style.paddingTop    = pad(-bb.y);
            s.wrap.style.paddingBottom = pad((bb.y + bb.height) - L.H);
            // lax: keep the scroll cue's fades off a lone number line, which
            // sits at the column edge and has to stay legible.
            const inset = (band, padPx) => band ? `${Math.round(band + parseFloat(padPx))}px` : '0px';
            s.frame.style.setProperty('--latex-fade-top',    inset(L.tagTop,    s.wrap.style.paddingTop));
            s.frame.style.setProperty('--latex-fade-bottom', inset(L.tagBottom, s.wrap.style.paddingBottom));
        }
    }
}

// Paint every segment regardless of the viewport — for printing, where nothing may
// be left as an empty placeholder.
function paintDocument(fontInfo, cache) {
    if (!cache.layout) return;
    cache.stats = { created: 0, moved: 0, repositioned: 0, removed: 0 };
    for (let i = 0; i < cache.layout.laid.length; i++) paintSegment(fontInfo, cache, i);
}

// ── Initialisation ────────────────────────────────────────────────────────────

// Hang each picture's payload on the node that draws it, once per block, so
// the renderer never has to thread the document through every call.
// lax: a paragraph whose only ink is a \parbox — one vlist of the lines
// TeX broke at compile time (hlist subtype 1), stacked with interline
// glue — is rebuilt as the running text those lines were made from, so
// KP re-breaks it at the reader's width like any other paragraph. LIPIcs
// sets its captions this way (\parbox to \hsize); left as a box the
// caption would keep the compiled measure and overhang the column. The
// lines' own line-end furniture goes — \leftskip and \rightskip (their
// stretch is remembered as the paragraph's alignment), \parfillskip, the
// penalties between lines — and the lines are joined by an inter-word
// space cloned from the text, except after a line that ended in its own
// fill (a \\), which keeps its forced break, and after a hyphen TeX
// inserted at the line end, which becomes a discretionary again. Runs
// once, over the decoded document, before any layout (initBlock).
const HL_LINE = 1;
const GLUE_LEFTSKIP = 8, GLUE_RIGHTSKIP = 9, GLUE_SPACE = 13, GLUE_PARFILL = 15;
function unboxPresetParagraph(para) {
    const nodes = para.nodes;
    let vi = -1;
    for (let i = 0; i < nodes.length; i++) {
        const n = nodes[i];
        if (n.type === 'vlist') { if (vi >= 0) return false; vi = i; continue; }
        if (n.type === 'glue' || n.type === 'kern' || n.type === 'penalty' || n.type === 'mark' || n.type === 'fnref' || n.type === 'local_par') continue;
        if (n.type === 'hlist' && !(n.children && n.children.length)) continue;   // the \parindent box
        return false;
    }
    if (vi < 0) return false;
    const lines = [];
    for (const c of nodes[vi].children || []) {
        if (c.type === 'hlist' && c.subtype === HL_LINE) lines.push(c);
        else if (c.type === 'glue' || c.type === 'kern' || c.type === 'penalty') continue;
        else return false;
    }
    if (!lines.length) return false;
    const out = [];
    let space = null, leftFil = false, rightFil = false;
    const isFil = g => g.type === 'glue' && (g.stretch_order || 0) > 0;
    const firstGlyph = ns => ns.find(n => n.type === 'glyph' || n.type === 'hlist' || n.type === 'disc');
    lines.forEach((ln, k) => {
        const ch = (ln.children || []).slice();
        if (ch.length && ch[0].type === 'glue' && ch[0].subtype === GLUE_LEFTSKIP) { if (isFil(ch[0])) leftFil = true; ch.shift(); }
        while (ch.length) {
            const t = ch[ch.length - 1];
            if (t.type === 'glue' && (t.subtype === GLUE_RIGHTSKIP || t.subtype === GLUE_PARFILL)) {
                if (t.subtype === GLUE_RIGHTSKIP && isFil(t)) rightFil = true;
                ch.pop(); continue;
            }
            if (t.type === 'penalty') { ch.pop(); continue; }
            break;
        }
        for (const n of ch) if (n.type === 'glue' && n.subtype === GLUE_SPACE && !(n.stretch_order > 0)) space = n;
        if (k > 0) {
            const prev = out[out.length - 1];
            if (prev && isFil(prev)) {
                out.push({ type: 'penalty', penalty: -10000 });
            } else if (prev && prev.type === 'glyph' && (prev.char === 45 || prev.char === 0x2010)
                       && firstGlyph(ch) && firstGlyph(ch).type === 'glyph') {
                out.pop();
                out.push({ type: 'disc', subtype: 0, pre: [prev], post: [], replace: [] });
            } else {
                // A clone: the paint reconciler keys elements by node identity.
                out.push(space ? { ...space } : { type: 'glue', subtype: GLUE_SPACE, width: 218453, stretch: 109226, shrink: 72818 });
            }
        }
        for (const n of ch) out.push(n);
    });
    nodes.splice(vi, 1, ...out);
    if (!para.align) para.align = leftFil && rightFil ? 'center' : leftFil ? 'right' : rightFil ? 'left' : para.align;
    return true;
}
function unboxPresetParagraphs(doc) {
    for (const p of doc.paragraphs) if (p.nodes && p.nodes.some(n => n.type === 'vlist')) unboxPresetParagraph(p);
}

function resolvePictures(doc) {
    const pics = doc.pictures;
    if (!pics || !pics.length) return;
    const walk = nodes => {
        for (const n of nodes) {
            if (n.type === 'picture' && n.picture) n.pic = pics[n.picture - 1];
            for (const k of ['children', 'replace', 'pre', 'post']) {
                if (n[k]) walk(n[k]);
            }
        }
    };
    for (const p of doc.paragraphs) walk(p.nodes);
    for (const it of doc.content || []) if (it.box) walk(it.box.children || []);
}

// The page embeds latex.proto as base64 text as its self-description.
// lax: upstream parses it into a protobuf.js type here; this viewer decodes
// with the fixed-schema wire decoder below instead (see modification 5 in
// the header), so the island is only required to be present.
function loadSchema() {
    const el = document.getElementById('latex-schema');
    if (!el?.dataset.schemaB64) throw new Error('#latex-schema element with data-schema-b64 not found');
}

// lax: ── fixed-schema proto2 wire decoder ─────────────────────────────────
// Decodes latex.Document for the schema generation this viewer supports
// (supported-schemas.json), producing exactly the shape protobuf.js
// toObject({defaults:false, arrays:true, enums:String, longs:Number}) gave:
// only wire-present fields are set (proto2 presence — gW relies on
// width === undefined), repeated fields are always arrays, enums decode to
// their lowercase names, doubles round-trip. Field numbers and kinds are
// latex.proto's, transcribed; test/latex-decode.test.ts in the site
// repository proves byte-for-byte equivalence against protobuf.js over the
// committed fixture block.
const LAX_ENUMS = {
    // lax: `mark` is NodeType's wire name for a \laxmark whatsit and `fnref`
    // its name for a footnote's reference point — proto2 scopes enum value
    // names to the package, so neither can reuse ItemKind's `marker` and
    // `footnote_ref`.
    NodeType: ['glyph','glue','kern','rule','hlist','vlist','disc','penalty','math','picture','transform','mark','fnref'],
    ItemKind: ['paragraph','display','vspace','marker','footnote_ref'],
};
const LAX_MESSAGES = {
    Document: {
        1: ['fonts','rep','FontInfo'], 2: ['paragraphs','rep','Paragraph'], 3: ['content','rep','ContentItem'],
        4: ['pictures','rep','Picture'], 5: ['glyph_metrics','rep','GlyphMetrics'],
    },
    FontInfo: { 1: ['id','u32'], 2: ['name','str'], 3: ['size_sp','u32'], 4: ['filename','str'] },
    GlyphMetrics: { 1: ['width','i32'], 2: ['height','i32'], 3: ['depth','i32'] },
    Picture: { 1: ['svg','str'], 2: ['vb_w','dbl'], 3: ['vb_h','dbl'] },
    Paragraph: {
        1: ['nodes','rep','Node'], 2: ['indent','i32'], 3: ['baselineskip','i32'],
        4: ['lineskip','i32'], 5: ['lineskiplimit','i32'], 6: ['align','str'],
        // lax: the \parshape band's width (sp), the only statement of a
        // paragraph's right inset (see paraBand). Absent in bundles sealed
        // before the schema gained the field.
        7: ['width','i32'],
        // lax: a footnote's paragraphs carry its ordinal here — the `n` of the
        // `fnref` node or `footnote_ref` item at the reference point. Absent
        // on body paragraphs, and in bundles sealed before the field.
        8: ['footnote','i32'],
    },
    ContentItem: {
        1: ['kind','enum','ItemKind'], 2: ['para','u32'], 3: ['box','msg','Node'], 4: ['amount','i32'],
        5: ['display_width','i32'], 6: ['display_indent','i32'], 7: ['display_shift','i32'],
        8: ['side','str'], 9: ['n','u32'],
    },
    Node: {
        1: ['type','enum','NodeType'], 2: ['char','i32'], 3: ['font','u32'], 4: ['width','i32'],
        5: ['height','i32'], 6: ['depth','i32'], 7: ['stretch','i32'], 8: ['shrink','i32'],
        9: ['stretch_order','u32'], 10: ['shrink_order','u32'], 11: ['subtype','u32'], 12: ['kern','i32'],
        13: ['shift','i32'], 14: ['glue_set','dbl'], 15: ['glue_sign','u32'], 16: ['glue_order','u32'],
        17: ['children','rep','Node'], 18: ['pre','rep','Node'], 19: ['post','rep','Node'], 20: ['replace','rep','Node'],
        21: ['penalty','i32'], 22: ['surround','i32'], 23: ['color','str'], 24: ['picture','u32'],
        25: ['leader','msg','Node'], 26: ['m_a','dbl'], 27: ['m_b','dbl'], 28: ['m_c','dbl'], 29: ['m_d','dbl'],
        30: ['cite','u32'], 31: ['citetarget','u32'], 32: ['metrics','u32'], 33: ['side','str'], 34: ['n','u32'],
    },
};
const laxUtf8 = new TextDecoder();

function laxDecode(bytes, typeName, depth) {
    if (depth > 500) throw new Error('block nests too deeply');
    const fields = LAX_MESSAGES[typeName];
    const out = {};
    for (const key of Object.keys(fields)) if (fields[key][1] === 'rep') out[fields[key][0]] = [];
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    let pos = 0;
    // A varint's low 32 bits (all this schema's varint fields are 32-bit;
    // a negative int32 arrives as a 10-byte two's-complement varint whose
    // high bytes only need consuming).
    const varint = () => {
        let lo = 0, shift = 0, byte;
        do {
            if (pos >= bytes.length) throw new Error('truncated varint');
            byte = bytes[pos++];
            if (shift < 32) lo = (lo | ((byte & 0x7f) << shift)) >>> 0;
            shift += 7;
            if (shift > 70) throw new Error('malformed varint');
        } while (byte & 0x80);
        return lo;
    };
    while (pos < bytes.length) {
        const tag = varint();
        const spec = fields[tag >>> 3];
        const wire = tag & 7;
        if (wire === 0) {
            const lo = varint();
            if (spec) {
                const [name, kind, extra] = spec;
                if (kind === 'u32') out[name] = lo;
                else if (kind === 'i32') out[name] = lo | 0;
                else if (kind === 'enum') out[name] = LAX_ENUMS[extra][lo] !== undefined ? LAX_ENUMS[extra][lo] : lo;
            }
        } else if (wire === 1) {
            if (pos + 8 > bytes.length) throw new Error('truncated fixed64');
            if (spec && spec[1] === 'dbl') out[spec[0]] = view.getFloat64(pos, true);
            pos += 8;
        } else if (wire === 2) {
            const length = varint();
            if (pos + length > bytes.length) throw new Error('truncated field');
            const chunk = bytes.subarray(pos, pos + length);
            pos += length;
            if (spec) {
                const [name, kind, extra] = spec;
                if (kind === 'str') out[name] = laxUtf8.decode(chunk);
                else if (kind === 'msg') out[name] = laxDecode(chunk, extra, depth + 1);
                else if (kind === 'rep') out[name].push(laxDecode(chunk, extra, depth + 1));
            }
        } else if (wire === 5) {
            if (pos + 4 > bytes.length) throw new Error('truncated fixed32');
            pos += 4;
        } else {
            throw new Error(`unsupported wire type ${wire}`);
        }
    }
    return out;
}

// Optional: {original filename → served filename} written into the page as a JSON
// island (prebuild.py / build.py). Lets a modified font be fetched from its
// renamed, content-hashed file while blocks still refer to it by its original
// name. Absent → registerFonts falls back to the original name.
function loadFontMap() {
    const el = document.getElementById('latex-font-map');
    if (!el) return;
    // Optional base for @font-face URLs. Defaults to the site root ('/fonts/');
    // a site served under a subpath (GitHub Pages project site, reverse proxy)
    // sets this to the right prefix so fonts don't 404.
    const base = el.getAttribute('data-fonts-base');
    if (base) fontBase = base.endsWith('/') ? base : base + '/';
    if (!el.textContent.trim()) return;
    try { fontUrlMap = JSON.parse(el.textContent); }
    catch { fontUrlMap = {}; }
}

// Decode one block into the kiwi decode shape the renderer reads: unset
// scalars absent (proto2 presence — gW relies on width===undefined), empty
// repeated fields as [] (not undefined), enums as the lowercase names the
// renderer compares against ('glyph', 'display'), ints as plain numbers.
function decodeBlock(bytes) {
    // lax: through the fixed-schema wire decoder (see loadSchema above).
    return laxDecode(bytes, 'Document', 0);
}

// lax: a block's bytes come embedded (data-nodelist-b64) or, past the page's
// embed budget, from a same-origin file (data-nodelist-src) — the page CSP's
// connect-src 'self' covers the fetch.
async function blockBytes(el) {
    if (el.dataset.nodelistB64) return b64ToBytes(el.dataset.nodelistB64);
    const src = el.dataset.nodelistSrc;
    if (!src) throw new Error('Missing data-nodelist-b64 or data-nodelist-src attribute');
    const response = await fetch(src);
    if (!response.ok) throw new Error(`block fetch failed: HTTP ${response.status} for ${src}`);
    return new Uint8Array(await response.arrayBuffer());
}

async function initBlock(el) {
    const t0        = performance.now();
    const doc       = decodeBlock(await blockBytes(el));
    resolvePictures(doc);
    unboxPresetParagraphs(doc);   // lax: \parbox paragraphs become running text
    const t1        = performance.now();
    const fontsData = Object.fromEntries(doc.fonts.map(f => [String(f.id), f]));
    // lax: register now, wait later — the layout below needs no browser
    // font (it reads the document's own glyph metrics), only the paint does.
    const { fontInfo, ready: fontsReady, stillPending } = registerFonts(fontsData);
    const t2        = performance.now();

    const params  = paramsFromEl(el);
    const widthPt = el.dataset.latexWidth
        ? parseInt(el.dataset.latexWidth)
        : (el.clientWidth / ZOOM) || DEFAULT_WIDTH_PT;
    // holdPaint (lax): no segment paints — not the first paint below, not the
    // IntersectionObserver's, not a resize's — until the faces have settled.
    const cache = { bcs: null, dom: null, layout: null, stats: null, holdPaint: true };  // bcs: Map(paraIdx → break candidates), built lazily
    // lax: the sidenote measure, if the page has already set one.
    const fnWidthPt = footnoteWidthFromEl(el);
    const data  = { doc, fontInfo, lastWidth: widthPt, lastAlign: params.align, lastFnWidth: fnWidthPt, params, cache, painted: false };
    blockData.set(el, data);
    // Layout first (this sets the svg's final height), then decide from the
    // block's resulting position whether to paint now or on approach. Blocks
    // are initialised top to bottom, so earlier blocks already have their
    // final heights when later ones measure their distance to the viewport.
    el.replaceChildren(layoutDocument(fontInfo, doc, widthPt, { ...params, footnoteWidthPt: fnWidthPt }, cache));
    const t3 = performance.now();
    // lax: the block now has its final height (the segments' <svg>s are
    // sized, and empty). Hold the first paint until the faces have arrived
    // — or the wait has run out — so the reader never sees the document set
    // in a fallback face and then jump as it is repainted.
    await fontsReady;
    if (stillPending()) fontsPending = true;
    cache.holdPaint = false;
    // Paint the segments near the viewport now; layoutDocument has already set the
    // IntersectionObserver watching the rest, which paint (once, for good) as they
    // are scrolled toward. Never un-painted.
    paintVisibleNow(fontInfo, cache);
    data.painted = true;
    observedBlocks.add(el);
    // lax: the block is in the document now — pin the in-paragraph anchors
    // and let the page place its cards.
    placeAnchors(cache);
    el.dispatchEvent(new CustomEvent('latex-viewer:reflow', { bubbles: true }));
    const t4 = performance.now();
    ro.observe(el);
    // A segment is the paint unit: a run of consecutive text paragraphs, or a single
    // display. The rest are painted as they approach the viewport (segIO).
    const segTotal   = cache.dom.segs.length;
    const segPainted = cache.dom.segs.reduce((n, s) => n + (s.painted ? 1 : 0), 0);
    return { decode: t1 - t0, fonts: t2 - t1, layout: t3 - t2, paint: t4 - t3,
             total: t4 - t0, segTotal, segPainted };
}

async function init() {
    // lax: fetched blocks (data-nodelist-src) count too.
    const blocks = [...document.querySelectorAll('[data-nodelist-b64], [data-nodelist-src]')];
    if (blocks.length === 0) return;

    const tStart = performance.now();
    installColorMaps();
    installCitations();
    loadSchema();
    loadFontMap();

    // Sequential to avoid font registration races
    let idx = 0, segPainted = 0, segTotal = 0;
    for (const el of blocks) {
        try {
            const t = await initBlock(el);
            segPainted += t.segPainted; segTotal += t.segTotal;
            console.log(`[latex-viewer] block ${++idx}/${blocks.length}: ${t.total.toFixed(1)} ms `
                + `(decode ${t.decode.toFixed(1)}, fonts ${t.fonts.toFixed(1)}, layout ${t.layout.toFixed(1)}, paint ${t.paint.toFixed(1)}) `
                + `— ${t.segPainted}/${t.segTotal} segments painted`);
        }
        catch (e) { el.textContent = `Render error: ${e.message}`; console.error(e); }
    }
    const segDeferred = segTotal - segPainted;
    console.log(`[latex-viewer] ${blocks.length} block(s) in ${(performance.now() - tStart).toFixed(1)} ms `
        + `· ${segPainted}/${segTotal} segments painted`
        + (segDeferred ? `, ${segDeferred} deferred (painted on scroll)` : ''));

    // Cold cache: at least one face was still loading when we first painted, so
    // some SVG glyphs may be showing in a fallback. Faces can finish in several
    // waves, and content keeps painting as the reader scrolls, so repaint on every
    // loadingdone wave (and once more when all faces settle) rather than a single
    // time — see scheduleFontRepaint. Guarded by fontsPending so a warm load, where
    // the first paint is already correct, does none of this.
    if (fontsPending && document.fonts) {
        if (document.fonts.addEventListener) document.fonts.addEventListener('loadingdone', scheduleFontRepaint);
        if (document.fonts.ready) document.fonts.ready.then(scheduleFontRepaint);
    }
}

document.addEventListener('DOMContentLoaded', init);

// lax: the fixed-schema decoder, exposed for the site's equivalence tests
// (test/latex-decode.test.ts proves it against protobuf.js) and for console
// debugging, with the segmentation and the anchor walk beside it for the
// same tests. Two calls are for a page that mounts segments elsewhere
// (footnotes as sidenotes): `reflow(el)` re-lays out a painted block if
// its width, alignment, or sidenote measure changed (reflowBlock's own
// test) and says whether it did; `paint(el)` paints whatever of the block
// is near the viewport and still unpainted or dirty — a segment the page
// has just moved from the end of the document to beside its reference,
// which the re-layout's own pass found far off screen.
if (typeof window !== 'undefined') window.laxLatexViewer = {
    decodeBlock, segmentsOf, containsMark, anchorSink, renderNodes, useGlyphMetrics,
    reflow(el) {
        const data = blockData.get(el);
        return Boolean(data && data.painted && reflowBlock(el));
    },
    paint(el) {
        const data = blockData.get(el);
        return data && data.painted ? paintVisibleNow(data.fontInfo, data.cache) : 0;
    },
};

})();
