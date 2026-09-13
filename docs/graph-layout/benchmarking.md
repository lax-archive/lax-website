# Corpus evidence and optional comparators

The immutable corpus is `test/fixtures/graph-layout/corpus.json`. It contains
1,516 distinct public graph views, their page occurrences, renderer/database
revisions and a split frozen before candidate selection. Scripts copy `split`,
`splitGroup`, `stratum` and all edge incidences unchanged. The 13 graphs in
`diagnostics.json` are explicitly synthetic examples and never count as archive
or held-out results. No script reads or edits archive records.

## Reproducing the evidence

Build the TypeScript modules, then invoke the development script:

```sh
npm run build
GRAPH_CHROME=/path/to/pinned/chrome node scripts/graph-benchmark.mjs --cold-labels
```

The browser must match `PINNED_GRAPH_BROWSER_VERSION` in `graph-measure.ts`.
The default corpus is the frozen fixture; the default old-output directory is
`/tmp/lax-graph-evidence/before`; results go to
`/tmp/lax-graph-evidence/benchmark`. `--corpus`, `--before`, `--out` and
`--measurement-cache` select explicit paths. `--id` and `--limit` produce a
clearly marked subset, which cannot claim full corpus coverage. `--no-synthetic`
omits only the separate diagnostic cohort. The script never changes a profile
or tunes on held-out results.

By default the benchmark also asks for the bounded nondominated geometry
frontier and saves each complete alternative as `ID.candidate-N.geometry.json`,
SVG and an inspectable page, with manifest links in the row/gallery. This adds
development-only validation, memory and output work beyond the archive build.
The report flags that work explicitly. Use `--no-retain-candidates` in a separate
output directory for a leaner timing pass; neither timing mode includes the
rest of the site build. No profile selection is made from held-out results.

All permitted labels and numbered dock text are projected first and measured in one batched service
using the site's actual SVG font contract. A cold layout pass always computes
the custom layout, including exact layer polishing and routing candidates.
`--cold-labels` also creates a fresh label-cache directory for a genuinely cold
measurement pass. Without it, the report states the actual label hits/misses;
a cold layout pass is not automatically a cold font measurement. A second
service reads the same label cache for the warm pass. Every cached geometry is
hashed and independently validated before use. Cold/warm geometry byte digests
must agree, and all cache misses/corruption/fallback computations are reported.

Canonical artifacts and observations are separate:

| Artifact | Contents |
| --- | --- |
| `manifest.json` | Corpus and source hashes, revisions, frozen split policy, engine/profile/selection versions, complete graph IDs and coverage |
| `graphs/ID.input.json` | Immutable measured input and public display mapping, retained even if layout fails |
| `graphs/ID.geometry.json` | Quantized, serialized/read-back, validated geometry; no host or timing fields |
| `graphs/ID.svg`, `.html` | Canonical SVG source and a rendered page with report-local CSS/fonts at 100% scale; no screenshot is implied |
| `assets/` | The site stylesheet, referenced font files, licenses and container-only scrolling rules; no browser script or layout library |
| `rows.jsonl` | One complete metric/diagnostic row for every requested view |
| `summary.json`, `report.md` | Separate archive/tuning/held-out/synthetic summaries, failures and every per-metric regression |
| `performance.jsonl`, `performance.json` | Per-graph cold/warm timings, inclusive phase distributions, operation counts, cache behavior and declared host conditions |
| `fatal-diagnostics.json` | A host/measurement failure that aborts preparation, without claiming a complete report |

The output directory is not an atomic deployment target. JSONL rows are written
incrementally so an interrupted benchmark retains its diagnostic evidence.
Neither `_site/` nor a published site is changed. Run into a new `--out` directory
when preserving an earlier comparison.

The entire report directory can be moved or served without the repository.
Rendered HTML pages link only to report-local stylesheet/font assets and allow
horizontal/vertical scrolling without shrinking text. Raw `.svg` files retain
the serializer's canonical bytes and are labeled **SVG source**; they are not
presented as styled self-contained drawings. Valid comparator diagrams use the
same serializer and portable report assets.

## Frozen metric definitions

`metrics-schema.json` and `METRICS_VERSION = final-geometry-v1` define report
rows. Values come from the independent final-geometry validator, after 0.001px
quantization and SVG serialization/read-back. Adaptive quadratic flattening has
a maximum 0.01px deviation, included in obstacle-clearance checks. Ordering's
dummy-segment crossing count is never used as the final crossing result.

| Metric | Definition |
| --- | --- |
| `crossings` | Proper pairwise route crossing events, deduplicated across adjacent segments; an actual common terminal is exempt only at that point |
| `repeatedCrossingPairs` | Distinct original edge pairs with more than one proper crossing |
| `endpointTouches` | Non-exempt events where one route ends at the event |
| `tangencies` | Contacts whose incident rays do not alternate |
| `multiwayCrossings` | Proper crossing sites occupied by more than two original edges |
| `overlaps` | Edge pairs with positive-length coincident runs |
| `bends` | Geometric direction changes; one rounded corner counts once, not once per flattening segment |
| `length` | Complete final route length at the documented curve approximation tolerance |
| `width`, `height` | Published drawing bounds, including the renderer's own margins/container minimums; `contentBounds` is also retained for the new graph |
| `minimumCrossingAngle` | Smallest acute angle at a proper crossing, or null when there are no proper crossings |
| `D` | Sum of `rank(target)-rank(source)-1` for unit-minimum-span edges of the displayed condensation DAG; SCC internal edges are excluded and separately counted |

Semantic node/edge/proof/statement counts, measured display nodes/edges/ports,
numbered docks, weak components, SCC sizes, degree histograms, label dimensions,
selected total edge span and per-component ranks accompany every result. The
search's maximum expanded rank width/dummy count is explicitly distinct from
the selected geometry's real-node widths and D. Operation counters are retained
with candidate reports; they are not timing estimates. `dummyGaps` copies the
engine's selected ordering gap count, and coherent dummy-chain moves remain a
separate operation counter. `permutationTrials` records complete fixed-rank
ordering candidates actually explored by the bounded permutation escape.
None of these counters is substituted for final crossings.

Distributions use nearest-rank percentiles: sorted element `ceil(p*n)-1`, with
null percentiles for an empty cohort. Timings are milliseconds. Core phase
durations are inclusive and may nest; summing them double-counts validation.
`layoutSearch` is the complete host-measured call, including component packing.
Node peak RSS uses `process.resourceUsage().maxRSS` on the declared Linux host;
it excludes Chrome and optional comparator processes. It is not a total-process-
tree memory claim. Uncontrolled concurrent host work is stated in performance
metadata. Browser paint, transfer, layout shift, keyboard/focus, pan/zoom and
mobile responsiveness require separate browser measurements.

## Comparing the actual old output

The baseline capture includes the old renderer's complete paths after its
post-layout ports, shortcuts and rounding. `graph-metrics.mjs` reconstructs
only the frozen entity-to-array mapping; it never reruns an idealized old
rank/order phase. Every recovered edge is checked against its captured terminal
positions and class before a comparison is considered usable. The legacy
proof-link ordering explicitly replays its en-US locale comparison; canonical
new IDs and the frozen split do not use that comparator.

Both renderers use 12px body labels. Numbered docks used 7.5px monospace in the
frozen baseline and now use measured 12px regular text. The old renderer truncated labels/identifiers;
the new renderer wraps full labels, so measured box dimensions can differ.
Metrics describe the entire old SVG at its native coordinate scale, and no
fit-to-page shrinking earns a compactness/readability improvement. Positive
after-minus-before deltas are listed individually for every cost metric, including
extra height, bends and length. A smaller minimum crossing angle is also a
regression when both diagrams have proper crossings; otherwise its delta is null
and the appearance/disappearance of crossings is stated without inventing an
angle comparison. A graph's failure is never removed from a
summary denominator.

The old proof adapter merged multiple statement assumptions belonging to one
concept. Such cases preserve their recorded multiplicities but receive no
numerical improvement verdict against a graph with distinct incidences. Missing
captures, missing objects and unverifiable attachments are likewise explicit.
The old capture lacks formal port constraints and arrowhead exclusion geometry;
only observed path/box/label collisions and geometry metrics are claimed for
it, not validation against the complete new production contract.

## Optional first-party-versus-library comparisons

`graph-baselines.mjs` is isolated development tooling. It neither installs an
engine nor enters the normal build or browser dependency graph. Current
comparison pins are Graphviz **2.43.0** and elkjs **0.12.0**. The latter must be
provisioned outside the repository:

```sh
npm install --prefix /tmp/lax-graph-comparators --no-save --package-lock=false elkjs@0.12.0
node scripts/graph-baselines.mjs --engine both --elk /tmp/lax-graph-comparators/node_modules/elkjs
```

The script consumes every saved measured input, including failed custom inputs
when present. It records its prepared-input coverage; this is not automatically
the full frozen corpus. Every parallel incidence has its own edge ID. ELK gets
the measured box sizes and explicit north/south/east/west ports, preserving fixed
positions or full fixed order when directly expressible. Mixed constraint groups
and expanded SCC envelopes are reported unsupported rather than approximated.
Its raw extended-edge JSON is saved before geometry conversion. The adapter is
based on the official [JSON/section contract](https://eclipse.dev/elk/documentation/tooldevelopers/graphdatastructure/jsonformat.html)
and [port constraints](https://eclipse.dev/elk/reference/options/org-eclipse-elk-portConstraints.html),
with the compound-layout limitations discussed in the full
[ELK paper](https://arxiv.org/html/2311.00533v1).

The dot comparator uses `rankdir=BT`, `splines=polyline`, fixed empty-label box
sizes and no edge concentration. It scales coordinates uniformly by 1,000
integer Graphviz points per pixel to preserve the measured 0.001px size quantum,
then reverses that numeric unit conversion. Arrow dimensions and spacing scale
with it. The old pinned Graphviz has a 65,535-point edge-coordinate limit in some
routing paths; cases hitting that limit are unsupported comparator rows, not
custom-engine failures. Fixed numbered docks/ports and SCC envelopes also need
a richer adapter and are not represented as flat approximations. The adapter
reads the actual polygon and normal-arrow-tip coordinates from
[Graphviz JSON](https://graphviz.org/docs/outputs/json/), following
[dot's documented attributes](https://graphviz.org/docs/layouts/dot/) and
[fixed-size behavior](https://graphviz.org/docs/attrs/fixedsize/).

Every comparator output receives the same independent geometry checks, and all
port, terminal-direction, overlap or size defects remain in its report. Its
geometry is never repaired by the custom router before scoring. A comparator's
strict-contract failure is not a claim that its unconstrained drawing algorithm
is wrong or inferior. Raw outputs permit review of unsupported cases and adapter
limitations without introducing either library into production.

No performance or visual acceptance target is claimed by this document.
Measured run reports and browser evidence own those conclusions.
