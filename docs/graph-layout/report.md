# Graph drawing implementation report

The corrected final corpus run validates all **1,529 requested graphs**. Among
1,514 comparable archive views, crossings improve on 136, remain equal on 1,378,
and increase on none. Other costs increase on 1,025 views; those regressions and
remaining large-drawing limitations are reported below. Requested delivery is
the [graph-drawing branch preview](https://laxarchive.org/previews/graph-drawing-19af3469/).
Build, browser and publication checks passed; the preview is live.

## Corpus and provenance

The frozen input contains **1,516 distinct archive views**: 1,427 concept graphs,
43 proof networks and 46 submission graphs. Its deterministic split is 1,010
tuning views and 506 held-out views. Thirteen diagnostic examples are synthetic
and are reported separately. Page occurrences and all semantic incidences remain
in [the frozen corpus](../../test/fixtures/graph-layout/corpus.json).

The baseline renderer revision is
`c7e3781cb5bc1b630b9c63f4d468bed3a344f48b`; the database revision is
`b1fca499b62be57f5d63df5a77fd72276e0e9fe3`. The split groups equal labeled
topologies, orders groups by SHA-256 within kind/size/dock strata, and holds out
every third group with offset one. It has not been reselected after evaluation.

The final quality report is `/tmp/lax-graph-evidence/final-quality-docks`, using
engine `lax-layout-1.0.4`, measurement contract `svg-labels-2` and pinned
Chromium `150.0.7871.124`. Its recorded source hashes were checked against the
current files with **zero differences**. The run began with HEAD
`1aee1535c52a9e267034daae9c5e11649106e911` and the integration changes present
but uncommitted; those source changes were subsequently committed as
`2ca14f1133b3511835efb0c0e3f6609dbbacecd9`. The manifest retains its actual start
revision. Its source-file hashes establish which implementation was measured.

```text
Corpus SHA-256:      1548a2d7d8826b37cb4055a42dab290e63e39d3dda38d9dacbcdc414a7ccdd96
Source-set SHA-256:  bfd1303a2cf02ee6ccb5abf43b2cab11e1811f0b73266ca4d95188dd47459f48
Measurement digest: bbf64eae60cf7a4559a985c0f0383c023745f7b4838761edd94fec8ba3424783
```

Earlier outputs under `final-quality` predate the complete numbered-dock and
post-insertion font readiness fixes and are stale development evidence. None of
their quality or timing totals is used here.

## Final geometry and regressions

| Cohort | Requested views | Valid / failed | Comparable old views | Crossings better / equal / worse | Any cost/angle regression |
| --- | ---: | --- | ---: | --- | ---: |
| Archive | 1,516 | 1,516 / 0 | 1,514 | 136 / 1,378 / 0 | 1,025 |
| Tuning | 1,010 | 1,010 / 0 | 1,009 | 94 / 915 / 0 | 666 |
| Held-out | 506 | 506 / 0 | 505 | 42 / 463 / 0 | 359 |
| Synthetic diagnostics | 13 | 13 / 0 | no archive baseline | no archive baseline | not compared |

Comparison uses the old renderer's actual completed SVG paths, including its
shortcuts. Body labels are 12px in both renderers. Old numbered docks used 7.5px
monospace; new docks use measured 12px regular text. New labels retain complete
permitted text and wrap, so measured boxes can differ. An old output with lost
or merged incidences, or unverifiable terminals, receives no numerical
improvement verdict.

Independent validation covers the quantized, serialized/read-back geometry.
Every requested graph retains its nodes, edges and actual attachments. The two
incomparable old outputs are retained explicitly:

| Graph ID | Baseline limitation |
| --- | --- |
| `25bca6b2c302ff99ce1a0bd1c7457e129fec86e7909842ca7a72ccba67f6e4b6` | The old proof adapter merged two `CycleObstruction` assumptions into one incidence. |
| `652c3d136fd0d3b25ac1f7b9b047914b99da6420fa6c2e8692f7a50f68f22e36` | The old capture contains zero nodes where the input requires one. |

All cost increases and defined crossing-angle decreases appear in the complete
1,025-row regression table in `final-quality-docks/report.md` and in
`regressions.json`. Undefined angles are not compared. The following counts
overlap because one view can regress on several metrics:

| Increased cost or reduced crossing angle | Archive views |
| --- | ---: |
| Height | 951 |
| Bends | 685 |
| Edge length | 636 |
| Width | 113 |
| Minimum crossing angle | 17 |

For example, the concept view on `lax-765601/index.html` (states `01`/`11`)
reduces crossings from 261 to 77, but expands from 7,475×310 to 12,146×1,160.
The proof network on `lax-68/index.html` reduces crossings from 9 to 2 and width
from 2,875 to 1,992, while height grows from 610 to 1,928. The concept view on
`lax-214022/index.html` (states `10`/`11`) retains one crossing while its minimum
angle drops from 33.05° to 18.25°. These are visible tradeoffs, not hidden
exceptions to an average improvement.

The archive's largest semantic/display graph has 82 nodes, 109 edges and 218
incidence ports. Maxima across the corpus are 27 docks, 22 weak components,
18 ranks, 34 real vertices in a rank, and 41 expanded vertices in a searched
rank. The largest selected dummy count D is 43; the largest total edge span is
148. Exact degree and label-dimension distributions remain in every row.
There are 2,911 retained complete archive review geometries and 26 synthetic
ones, all independently validated. Candidate reports retain rejected attempts
and their diagnostics too.

The diagnostic path is straight, with zero bends or crossings. The diamond,
repeated diamonds with skip edges, fan-in/out, numbered docks, alternative
proofs and concept-level assumption examples have zero crossings. The dense
bipartite example retains nine crossings and all its incidences. Complete
static SVG and metrics exist for all 1,529 views; the old capture includes
screenshots for all 1,516 archive views. Final interaction/screenshot capture
uses the declared interaction tier, not a claim that every new SVG was manually
inspected in a browser.

## Selected profile and operational limits

`readable-v1` uses the frozen `extent-then-crossings-v1` policy. The minimum-area
valid candidate defines an envelope of `max(960, 1.5 × width)`,
`max(720, 1.5 × height)` and `max(960 × 720, 2 × area)`. Eligible candidates are
ordered by final crossings, repeated crossing pairs, tangencies, bends, length
and area; crossing tolerance is zero. The numerical policy was not tuned on the
held-out views. [The implementation notes](README.md#selected-search-profile)
record its exact search and spacing budgets.

Exact layer ordering certifies only the fixed-neighbor subproblem, up to sixteen
movable vertices including dummies. Rank optimality concerns its rank objective
and requires checked termination. Bounded portfolio and routing searches make
no global drawing-optimality claim. Budget exhaustion retains a validated
feasible candidate or stops preparation with an explicit diagnostic. No archive
rank solve exhausted its pivot budget in the final run.

Large valid drawings retain 12px text and use scrolling/panning. The 500,000
expanded-vertex allocation guard is not an interactive performance guarantee.
Sparse long-edge storage and one-bend visibility graphs remain conditional
optimizations; dependencies are never dropped to fit a budget. Conservative
rank-channel reservation can increase height and bends, which remain reported.
There are 221 archive views with a `readability-overflow` diagnostic. Maximum
width and height are 12,146 and 1,928 respectively, on different views. The most
congested held-out example still has 168 crossings and a minimum angle of
0.795°, compared with 282 crossings before. Valid geometry does not establish
comfortable overview readability for that tier.

The frozen archive contains no display SCC. Expanded cycles are covered by
separate synthetic fixtures using complete member rows and distinct lanes.
The external-SCC example has nine crossings and three repeatedly crossing edge
pairs; the display-only cycle has fifteen crossings and five repeated pairs.
Their dimensions are 590×410 and 809×270. A compact SCC interior is not claimed.
The fallback preserves members, docks, gates and true arrow direction.

## Determinism, resources and browser behavior

The quality and lean runs have **1,529/1,529 identical measured inputs,
presentation payloads and selected geometry byte sequences**. Their graph ID
lists, frozen corpus, numerical profile, selection policy, measurement signature
and source-file hashes also agree, with no exceptions. The complete comparison
is `final-performance/run-equivalence.json`. Both runs retain the actual
starting revision `1aee1535c…`; the shared source digest is the one recorded
above, including the subsequently committed integration source.

The lean benchmark ran sequentially without concurrent project tests, builds
or other benchmarks. Ordinary desktop activity and filesystem caching were
not controlled, and no artificial CPU throttling was applied. Its reference
host was an Intel Core i7-8650U at 1.90GHz, eight logical CPUs, Linux
5.15.0-191-generic x64 and Node v22.14.0. Exact measurement used Chromium
150.0.7871.124. The Node process peak RSS was **577,089,536 bytes (550.36 MiB)**;
this excludes the measurement browser and is not a process-tree peak.

| Lean pass | Views valid / failed | Total seconds | Geometry hits / misses | Label hits / misses | Measurement batches / browser launches |
| --- | --- | ---: | --- | --- | --- |
| Cold | 1,529 / 0 | 351.506 | 0 / 1,529 | 0 / 616 | 3 / 1 |
| Warm | 1,529 / 0 | 3.879 | 1,529 / 0 | 616 / 0 | 0 / 0 |

Cold text measurement took 1.850s; complete preparation took 2.694s. Warm
measurement-cache access took 0.038s; complete preparation took 0.516s. Neither
pass observed a corrupt cache entry, a layout failure or a canonical byte
mismatch. Geometry hits are independently revalidated before use.

The complete cold layout search took 340.703s. Ordering accounts for 295.176s
(86.6% of that search time), and orthogonal routing including its validation
accounts for 33.539s (9.8%). The worst individual search took **22.790s**,
including 22.587s in ordering, on proof fixture `53f32829b057…`. Cold ordering
is the measured build bottleneck; the small median does not hide that tail.

The following durations are **milliseconds per graph**. They are inclusive
phase totals across that graph's components/candidates. Nested phase durations
must not be summed. A phase's count excludes graphs that do not run it.

| Pass | Phase | Count | p50 | p95 | Maximum |
| --- | --- | ---: | ---: | ---: | ---: |
| Cold | Complete layout search | 1,529 | 2.250 | 663.654 | 22,790.388 |
| Cold | Projection | 1,529 | 0.057 | 0.446 | 12.629 |
| Cold | Node sizing | 1,529 | 0.046 | 0.308 | 2.683 |
| Cold | Ranking | 1,528 | 0.024 | 0.098 | 1.002 |
| Cold | Proper graph | 1,528 | 0.020 | 0.113 | 1.176 |
| Cold | Ordering | 1,528 | 1.068 | 408.940 | 22,587.242 |
| Cold | BK coordinates | 1,528 | 0.102 | 1.447 | 8.428 |
| Cold | L1 coordinates | 1,528 | 0.047 | 2.266 | 64.455 |
| Cold | Corridors | 1,528 | 0.017 | 0.245 | 2.482 |
| Cold | Protected routing | 1,528 | 0.027 | 0.686 | 4.471 |
| Cold | Orthogonal routing, including validation | 994 | 1.259 | 72.210 | 2,680.422 |
| Cold | Rounding, including validation | 1,528 | 0.115 | 4.786 | 108.940 |
| Cold | Candidate validation | 1,528 | 0.052 | 8.672 | 180.924 |
| Cold | Final serialized validation | 1,529 | 0.078 | 3.946 | 99.333 |
| Cold | SVG serialization | 1,529 | 0.142 | 4.571 | 99.891 |
| Cold | Geometry-cache write | 1,529 | 0.278 | 1.517 | 8.961 |
| Cold | Old-output comparison | 1,516 | 0.080 | 1.152 | 43.238 |
| Warm | Projection | 1,529 | 0.051 | 0.366 | 3.670 |
| Warm | Node sizing | 1,529 | 0.032 | 0.222 | 1.359 |
| Warm | Geometry-cache read | 1,529 | 0.061 | 0.239 | 1.048 |
| Warm | Geometry-cache validation | 1,529 | 0.141 | 4.648 | 104.594 |

Recorded cold search work over all 1,529 views is:

| Operation | Count |
| --- | ---: |
| Rank pivots / exhausted rank solves | 196 / 0 |
| Coordinate pivots | 16,811 |
| Sweeps | 31,584 |
| Sifting moves | 1,050,208 |
| Exact DP states | 11,736,580 |
| Coherent-chain moves | 12,256 |
| Fixed-rank permutation trials | 64,434 |
| Routing expansions | 3,738,389 |
| Visibility vertices | 11,345,742 |
| Complete candidate evaluations | 6,837 |

The quality run retains review frontiers and incurs extra validation and output
work; its timings are development observations. The separate lean run omits
that work but still includes the benchmark's metric extraction, comparison and
artifact writes. Neither isolated graph pass is the complete website build.
All raw observations are in `final-performance/performance.json`; timings and
host names remain outside canonical geometry bytes.

The final browser run covers the declared 58-view tier: all 43 archive proof
networks, all 13 synthetic examples, and the largest concept and submission SVGs.
Before/after screenshots use 100% zoom and the same 720px graph viewport.
Chromium 150.0.7871.124 used the reference host above, 1280×900 desktop and
390×844 narrow viewports, reduced motion, and four-times CPU throttling for the
narrow tier. Local asset fulfillment measures rendering rather than internet
download latency. No other local build or benchmark ran during the final timing
pass. Its complete report, individual samples and screenshots are in
`final-browser/`.

| Measurement | Desktop | Narrow, 4× CPU throttling |
| --- | ---: | ---: |
| Highlight/inspector handler p95 | 3.7ms | 6.1ms |
| Handler maximum | 66.7ms | 38.7ms |
| Double-rAF next-paint proxy p95 | 33.7ms | 34.1ms |
| Zoom frame interval p95 | 16.7ms | 16.8ms |
| Pan frame interval p95 | 16.7ms | 16.7ms |
| Zoom intervals over 25ms / measured intervals | 1 / 1,972 | 6 / 1,972 |
| Pan intervals over 25ms / measured intervals | 1 / 1,938 | 0 / 1,938 |

The measured p95 handler target is met in both declared conditions, but 14 of
1,710 desktop handlers and 40 of 1,680 narrow handlers reached 8ms. The maximum
narrow zoom interval was 99.9ms. At a nominal 60Hz, rounding each interval to
frame periods estimates one missed desktop zoom frame and twelve narrow zoom
frames; pan estimates are one and zero. These are rAF observations, not direct
compositor dropped-frame measurements or a universal 60fps guarantee. The
double-rAF proxy is likewise distinct from actual compositor latency.

All 58 views have zero observed graph-induced layout shift and no page errors
or unexpected navigation. Public interaction is **21,851 bytes, 6,050 bytes
gzip**, below the 25KiB gzip budget. No third-party graph code or first-party
layout search engine was transferred. Default SVGs require no browser layout;
the separate local worker is covered by the packaged-renderer tests.

The largest tested SVG has 660 elements and 125,813 bytes of geometry. Its DOM
interactive time was 43.6ms and first contentful paint 60ms in the local harness.
Across the tier, these p95 values are 43.6ms and 64ms. Wide graphs still require
panning; full diagrams are retained as SVG rather than squeezed into screenshots.
The path, diamond, long-label proof, numbered docks, dense view and tooltips were
visually inspected. An early benchmark attempt selected a drag point before
reset's animation-frame paint; the corrected harness waits for that paint and
records unexpected navigation independently.

## Optional comparators and acceptance checks

Both optional comparators received all 1,529 complete measured inputs. Results
are in `final-comparators/`, with raw engine output and every unsupported case.

| Comparator | Valid | Strict-contract defects | Unsupported |
| --- | ---: | ---: | ---: |
| Graphviz 2.43.0 | 822 | 2 | 705 |
| elkjs 0.12.0 | 1,518 | 9 | 2 |

Graphviz's adapter reports 693 native scaled-coordinate limit cases and twelve
port/group cases as unsupported. Its 822 valid drawings tie the custom engine
on crossings. Against valid ELK drawings, custom crossings are lower on 49,
equal on 1,466 and higher on three. All three are held-out submission-dependency
views on `lax-132576`, `lax-157538` and `lax-916827`: custom has nine crossings,
ELK seven. The frozen custom policy was not retuned on these results. ELK's two
unsupported cases are expanded SCCs. Other defects concern terminal direction
and, for two dot outputs, port/arrow geometry. A strict-contract failure is not
a claim that an unconstrained drawing algorithm is inferior. Neither comparator
is a normal build or public browser dependency. The first sandboxed dot attempt
could not launch its process; the recorded final run used the available host
executable and verified its pin.

The normal build used all 55 records from the frozen database, including PDFs,
web-paper bundles and compiler references. The database checkout remained clean.
The build prepared 648 containers, 1,508 applicable states and 1,437 distinct
layouts. Its cold graph cache started empty; the warm run reused every layout.

| Build | Whole command, seconds | Graph preparation, seconds | Layout hits / misses | Label hits / misses |
| --- | ---: | ---: | --- | --- |
| Normal, cold graph cache | 328.908 | 323.011 | 0 / 1,437 | 0 / 569 |
| Normal, warm | 11.551 | 6.026 | 1,437 / 0 | 569 / 0 |
| Quick, 21 local records, reused cache | 16.040 | 13.666 | 385 / 84 | 165 / 19 |

Cold and warm normal builds produced **identical bytes for all 1,092 output
files**, including HTML, assets, inline geometry and alternate views. The
published-file manifest SHA-256 is
`ae60196bc5ad2685e162c70b36b33fa4d0963086ae4b3035ee13e77efc90b48a`.
The complete commands, logs, graph diagnostics and file hashes are in
`final-builds/`. The quick command includes the requested
`npm run site:build -- --no-papers --no-references` flags. Its cache was already
populated by the normal build; it is not reported as a cold build.

No public build used local layout fallback or a corrupt cache entry. Optional
orthogonal attempts reported 24 unavailable routes, six exhausted search budgets
and four rejected invalid candidates; the selected, published geometry remained
valid in every case. The normal build logs retain KaTeX metric warnings for
`𝓕` and `◇`. GNU time reported maximum RSS of 1,261,172 KiB for the cold build;
this is its process maximum observation, not simultaneous process-tree memory.
Atomic-output failure, cache corruption, anonymity, packaged local rendering,
preview prefixes and self-contained exports are covered by repository tests.

`npm run check` passes all 351 tests. Chromium, Firefox and WebKit each pass all
nine graph integration cases; [browser.md](browser.md) records exact versions,
screenshots, the font-readiness regression and runtime-specific test details.
The final check on the pushed implementation passed 351 tests in 21.51s.
[Deployment run 34730677774](https://github.com/lax-archive/lax-website/actions/runs/34730677774)
also passed its checks and real database build, deployed the preview and verified
the published tree. Direct HTTPS checks confirmed `preview.json` identifies
`graph-drawing` at implementation commit `2ca14f1133b3511835efb0c0e3f6609dbbacecd9`,
and the previews index links `graph-drawing-19af3469/`. Main was not merged.

The generated evidence index is `/tmp/lax-graph-evidence/index.html`; its portable
bundle is `/tmp/lax-graph-evidence/final-evidence.tar.gz`, with a SHA-256 sidecar.
It contains complete geometry/regression reports, optional comparators, the
equal-scale gallery, browser integration screenshots and build/test logs.
Generated sites and evidence remain outside Git. Frozen fixtures, source,
reproduction scripts, algorithm tests and this report are tracked on the branch.
