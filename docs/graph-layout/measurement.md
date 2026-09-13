# Exact graph label measurement

`src/sitegen/graph-measure.ts` owns host measurement, independently of the pure
layout core. `createGraphMeasurer()` creates one service for a complete build.
Call `measureLabels()` with all permission-filtered display labels; the service
deduplicates text/style requests, reads validated content-cache entries and
measures misses in batches of 256 in one lazily launched browser session.
Concurrent calls are serialized through that session. Always `close()` it in
the build's `finally` block. A fully cached build does not launch a browser.

The initial style is 12px, weight 400, letter spacing zero, line height 16px,
with a suggested caller wrapping width of 240px. Requests can specify 400 or
700 weight and measured alternative dimensions. Node padding, numbered docks,
attachment rails and port capacity belong to the separate measured-node
projection: label dimensions are not complete node dimensions.

`displayLabelRequests()` in `graph-node-size.ts` supplies the canonical batch
for preparation and benchmarks. It includes every visible numbered dock as a
decimal string in the same 12px regular style. Local descriptors carry that
same request list to the browser helper. The node-size pass reserves the
larger of a 20px minimum, exact numeral ink diagonal plus 8px padding,
and attachment capacity. Numeral ink is included in node-local `labelBoxes`,
and dock text uses the measured line baseline. Missing numeral metrics or a
wrapped/changed ordinal is a diagnostic; no central-baseline guess or silent
renumbering is used. Ordinary labels and dock numbers both serialize one
`text` element with positioned `tspan` lines, matching measurement.

Numbered statement docks are circles in a row below the concept box. Proof
conclusions terminate on the corresponding circle. Statement-level outgoing
incidences retain their exact identities and use separate lanes around the
left side of the body; those lanes are included in the measured envelope and
validated in ordinary routes and expanded display cycles. The readable-v2
profile reserves 12px between attachment positions and dummy tracks, with
32px between neighboring boxes. This widens routing channels without changing
the text size or dropping edges.

## Browser and font contract

The pinned archive host is Chrome for Testing **150.0.7871.124**, device scale 1, `en-US`, UTC,
with font hinting disabled. `GRAPH_CHROME` selects the executable;
`GRAPH_CHROME_VERSION` explicitly selects its expected full version. These also
have host options (`executablePath`, `expectedBrowserVersion`). The actual
browser version is checked after launch; a mismatch is a build diagnostic.
Changing a pin creates a new measurement namespace and requires fresh evidence.
The executable is provisioned by archive build tooling, never by the installed
renderer package. `playwright-core` is dynamically imported only on a host
cache miss; it is a development dependency, not a public browser asset.

Local library callers can set `hostBrowser: false`: exact cache hits and an
explicitly injected provider remain available, but a cache miss returns
`GraphMeasurementUnavailableError` without probing or importing browser
tooling. This avoids turning an unrelated installed browser into a mandatory
version requirement for local authoring. Host availability is not part of the
measurement key, so an archive cache remains usable through that local path.

The font stack, exported as `GRAPH_LABEL_FONT_FAMILY`, is:

1. The site's existing Latin Modern regular/bold WOFF2 fonts.
2. Latin Modern Math 1.959, GUST Font License, converted from OTF to WOFF2
   without modifying glyphs. Original copyright: B. Jackowski, P. Strzelczyk
   and P. Pianowski, 2012–2014, on behalf of TeX users groups.
3. DejaVu Serif 2.37, converted from TTF to WOFF2 without modifying glyphs,
   exposed under the CSS family `Lax Graph Fallback`. Its complete font
   license and copyright notice are in `assets/site/DEJAVU-FONT-LICENSE.txt`.

Greek letters and Unicode subscript digits are present in the frozen corpus
and absent from the original LM text fonts. The explicit fallback avoids
platform font choice. Latin Modern Math covers supplementary mathematical
alphabets; DejaVu covers the subscript digits and ordinary additional symbols.
The unmodified GUST notice already shipped with the site covers LM Math too.
Font binaries and their SHA-256 hashes are checked against
`assets/site/graph-fonts.json` before measurement. That manifest records the
Unicode `cmap` intervals extracted with FontTools 4.29.1; it is coverage
metadata, not a shaping implementation. Every input code point must be covered
by the selected regular/bold primary face or the explicit fallback faces.
Unsupported characters produce `GRAPH_LABEL_GLYPH_UNSUPPORTED` with code points
before browser launch; they never silently become missing-character boxes.

The helper explicitly loads each declared `FontFace`. For each batch it then
inserts temporary text using the actual requested styles, loads the matching
stylesheet-connected faces through `document.fonts.load()`, and awaits
`document.fonts.ready` **after text insertion**. Programmatically loaded font
objects do not establish that the stylesheet's separate face objects are
ready. The regression exposed early fallback bounds before those CSS faces
loaded; waiting for that exact readiness transition produced the correct ink.
All requests share this batch wait, with no animation-frame or timer delay.
The archive measurement page serves only
local asset bytes through intercepted same-origin requests; no network font or
CDN is involved. Browser tests additionally check Chromium's platform-font
provenance: tested Latin, Greek and subscript labels use custom bundled faces.

The SVG serializer must emit the same family, size, weight, letter spacing,
normal kerning and **`font-synthesis: none`**, left/start text anchoring, ordinary
alphabetic baselines, `text-rendering: geometricPrecision`, and one
`<tspan x="…" y="…">` per measured line. Applying
unrelated title, monospace, central-baseline or font-size CSS to those text
elements invalidates the measurement contract. Both the archive measurement
page and the local preview use the site's own stylesheet and its LM font-face
declarations. Tests re-emit the SVG in a second page with that same stylesheet.

## Wrapping and returned geometry

`assets/site/graph-measure-local.js` contains the single browser implementation.
The archive host invokes that exact asset. It measures the actual SVG text and
tspan structure through `getComputedTextLength()` and `getBBox()`, including
left overhang and the full SVG glyph envelope. It does not use character-count
width estimates or canvas approximations. The `ink` field is the conservative
SVG glyph box (which can include font side bearings), not a raster-pixel mask.
Version `svg-labels-2` measures the complete assembled text with all positioned
tspans after proposing line breaks. Isolated line probes do not necessarily
have the same fallback-font envelope as a complete multiline element. If the
assembled width exceeds the requested wrapping width, the helper tightens the
proposal and remeasures the whole result, with an explicit input-length work
budget and diagnostic on failure. This version changes cache signatures.

The actual-SVG regression also detected a separate viewport effect: CSS rounds
fractional SVG dimensions to its layout grid, which can give text a slightly
non-unit scale relative to the viewBox and alter hinted glyph advances. The
published outer geometry therefore has whole-pixel width and height. This
adds space only on the right and bottom; measured baselines, nodes, ports and
routes keep their coordinates.

Greedy wrapping uses measured complete candidate lines. Explicit newlines are
hard breaks; tabs and runs of ordinary spaces follow the documented display
whitespace normalization. Overlong words and identifiers wrap on Unicode
grapheme boundaries measured one prefix at a time, without ellipses or lost
characters. A single grapheme wider than the requested width is a diagnostic.
The complete original text remains in `LabelMetrics.text`. The accessibility
label and inspector can use that permitted text directly.

Each result contains a total width/height, a stable signature, and lines with
their own text, local x, actual baseline y and local glyph box. The first
baseline is derived from the measured LM font envelope and all actual line
glyphs, rather than a guessed fraction of font size. Subsequent baselines are
separated by the requested line height. Total bounds include any overhang from
exceptionally tall or low glyphs. Empty labels and explicit blank lines retain
their line-height envelope. The independent host validator checks finite
coordinates, full non-whitespace character preservation, and containment of
every glyph box. Node/route validation after quantization is a later stage.

## Caches and host injection

`graphMeasurementKey()` hashes original text, maximum width, all font/spacing
tokens, the font-file signature, measurement-source hash, and versioned browser
or injected provider identity. The site's `@font-face` declaration context is
hashed separately, in cascade order, because browser font selection can depend
on those declarations even with identical font bytes. Unrelated stylesheet
colors and layout rules do not change the measurement key. All canonical data uses fixed field order; no
locale sort, timestamp, wall-clock measurement or machine name appears in it.
Each cached record contains a payload digest and is validated again on read.
Malformed, truncated, mismatched or geometrically invalid entries become cache
misses, are measured again, and are atomically replaced. Cold and warm results
have identical bytes. Statistics (elapsed time, labels, hits, misses, corrupt
entries, batches and launches) are separate and must not be serialized into
geometry or public cache manifests.

A hosting environment may inject `MeasureLabelsProvider` plus a stable
`providerId`. This interface receives normalized requests and the font/style
environment, and returns complete exact `LabelMetrics` in request order. It
does not authorize approximate character-count metrics. Results and cache hits
share the same validation. Provider signatures are obtained with
`graphMeasurementKey(request, environment.signature)`.

## Local authoring fallback

Only `GraphMeasurementUnavailableError` means the host lacks usable browser
tooling. The site generator may catch it **in explicit local-preview mode** to
publish the separate first-party browser/worker payload. Archive builds must
fail on missing metrics; pin, font and geometry errors are not permission to
publish approximate archive output.

The local entrypoint loads `graph-measure-local.js` and calls
`laxGraphMeasure.measureLabels(requests, environment, {local: true})`. It gets
the exact same wrapping/measurement method with the page's bundled fonts, then
passes measured nodes to the separately packaged custom-core worker. The
measurement asset itself imports no core or layout library. Ordinary public
interaction must import neither local asset nor worker. Local signatures add
the local browser identity, so results cannot be mistaken for pinned archive
measurements. The environment carries font metadata only, never unfiltered
archive labels, URLs, authors or private source metadata.

Relative font URLs resolve against the helper's own script directory. A host
may provide `assetBaseUrl`; the raw measurement helper can also consume data
URLs on its `fontFaces` entries when its origin provides Web Crypto. This
helper capability does not make the complete graph worker fallback available
under `file:`. Fresh local graphs require an HTTP localhost preview, such as
`lax serve`; `graph-local.js` diagnoses a file URL explicitly. Prepared
self-contained file exports already contain their SVG and alternate views
and use neither measurement nor a worker. The helper never fetches a remote
engine. Source, font coverage metadata and fonts are in the renderer's existing
`assets/` package, so local authors need no browser-binary installation step.

## Evidence

`test/graph-measure.test.ts` checks shared normalization/keys, immutable metrics,
cache batching and corruption recovery, unavailable-tooling diagnostics, font
coverage, and exact-browser results. The browser cases cover proportional
widths, long identifiers, multiline and empty labels, combining clusters,
bold/letter-spaced fallback text, SVG re-emission, and archive/local equality.
Actual tspan boxes are checked independently in a second page, and system-font
fallback is rejected via Chromium font provenance. The browser test reports a
skip when no executable is installed; archive integration must provision the
pin and run these cases. `graph-browser.test.ts` also checks the actual emitted
SVG for a multiline label and a ten-digit dock ordinal: ink fits the circle,
the measured baseline is preserved, and numbered statement attachments and
links remain distinct. This document makes no corpus-wide time or transfer
claim; build and browser benchmark reports own those measured results.
