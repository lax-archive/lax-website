# Custom graph drawing

Implementation branch: `graph-drawing`, starting at
`c7e3781cb5bc1b630b9c63f4d468bed3a344f48b`.
The specification supplied on 12 September 2026 is the acceptance contract.
This document records implementation decisions and evidence, not unmeasured
quality claims. Nothing on this branch authorizes deployment.

The public path is permission-filtered presentation data → measured semantic
ports and nodes → bounded deterministic search → independent quantized geometry
validation → inline SVG. Interaction consumes prepared geometry. Labels, links,
statuses and permitted inspector content belong to presentation, never the
layout core. The local renderer has a separate first-party measurement/worker
fallback; archive pages must never load it.

## Boundaries and contracts

| Layer | Responsibility |
| --- | --- |
| `src/sitegen/graph-project.ts` | One immutable display projection from already permission-filtered page payloads; semantic nodes, proofs, statement docks and every incidence retain their IDs. |
| `graph-measure.ts`, `graph-node-size.ts` | Batched browser measurement with bundled fonts, wrapped SVG lines, ink bounds, dock capacity and visible attachment rails. |
| `src/graph-layout/` | Pure normalization, components, rank/order search, port-aware coordinates, protected/orthogonal routes, safe rounding and selection. |
| `validate.ts` | Independent checks of the complete reference and quantized serialized geometry, including arrowheads, groups and actual route crossings. |
| `graph-prepare.ts`, `graph-svg.ts` | Validated geometry caching, at most four applicable ancestry states, static SVG with real anchors, and permitted interaction payloads. |
| `assets/site/graph-interaction.js` | Precomputed incident highlighting, inspectors, viewport transforms, fullscreen and complete view replacement. |
| `graph-local.js`, `graph-local-worker.ts` | Separately packaged local-only measurement/worker fallback using the same pure core. |

Every point in published geometry uses root SVG coordinates. Rectangles use
top-left positions; port offsets and label boxes are node-local top-left
coordinates. Internal placement centers never escape as ambiguous public port
offsets. Rank increases from a dependency to its user and maps to decreasing y;
semantic edge direction is never reversed. Containing SCC groups are separate
from obstructing member footprints. The schema is in
[`types.ts`](../../src/graph-layout/types.ts).

Coordinates retain their 0.001-unit quantum. Final outer width and height round
up to whole units, adding empty space only at the right and bottom. This keeps
the SVG viewport equal to its viewBox at 100% scale: fractional CSS viewport
rounding otherwise changes the browser's glyph metrics despite unchanged text
positions. The actual serialized-SVG measurement regression checks this case.

Proof incidences retain the AND/OR structure and separate alternative proofs.
Numbered statements retain their fixed dock identities. The projection can
also represent a coarse concept assumption without inventing a statement.
Neither proof incidences nor direct import dependencies undergo transitive
reduction. Layout dummies, bends and group gates are never mathematical nodes.

Algorithm work was split only after the common geometry schema and independent
validator existed. [Ranking/ordering](rank-order.md),
[placement/routing](placement-routing.md), [expanded SCCs](expanded-scc.md),
[measurement](measurement.md), [browser checks](browser.md), and
[corpus/comparator tooling](benchmarking.md) document methods and verification.

## Selected search profile

`readable-v1` and `extent-then-crossings-v1` use one numerical policy for all
graph kinds. These values were frozen before evaluating the held-out split;
the implementation does not tune them per graph ID.

| Setting | Value and scope |
| --- | --- |
| Label size / line advance | 12px / 16px, exact measured wrapping at 240px; full permitted label remains accessible. |
| Label padding / row box gap | 10px / 28px. |
| Edge clearance / port separation | 8px / 8px; measured node capacity includes docks and rails. |
| Base rank gap / corner radius | 32px / at most 4px; traffic can enlarge bands, unsafe rounding is rejected. |
| Rank pivots | 4,096 per weak component and rank solve; exhausted solves retain feasible ranks with a diagnostic. |
| Ordering restarts | Stable order, reverse and two fixed seeds; eight sweeps and 4,000 sift/permutation trials per seed budget. |
| Exact ordering | At most 16 vertices, including dummies; two million DP states per seed budget, with smaller contiguous windows on wide layers. |
| Complete geometry portfolio | At most 12 candidates per weak component; a beam preserves both original feasible and optimized rank assignments. |
| Orthogonal search | 100,000 expansions per candidate search, at most two stable route orders and two bounded rip-up trials. |
| Explicit expansion guard | 500,000 expanded vertices, checked before allocating dummy chains. This is an allocation guard, not a measured promise to render that tier interactively. |

The minimum-area valid candidate defines an eligibility envelope: width at most
`max(960, 1.5 × compact width)`, height at most
`max(720, 1.5 × compact height)`, and area at most
`max(960 × 720, 2 × compact area)`. Within it, selection minimizes final proper
crossings, repeated crossing pairs, tangencies, bends, length and area, in that
order. Crossing tolerance is zero. Cosmetic rounding must preserve the checked
quality constraints. Nondominated complete alternatives can be retained by
development reports. None of these steps claims global drawing optimality.

Large valid drawings use the same measured 12px text and a scroll/pan viewport;
`readability-overflow` reports bounds exceeding 960×720. Resizing and fullscreen
change the camera only. No graph-size cutoff drops nodes or edges. Unsupported
geometry or depleted expansion capacity stops preparation with a diagnostic,
before replacing the previous site output.

The frozen corpus contains no display SCC, so the expanded row-and-lanes
interior is validated on explicit synthetic group/port fixtures. A compact SCC
interior is not claimed. Sparse long-edge storage, gap-restricted ordering and
one-bend visibility graphs remain conditional optimizations: this branch does
not label a different shortcut as an implementation of those papers. The
coherent-chain phase reports dummy gaps without claiming gap optimality.

## Operational behavior

Public archive builds require exact measurement from pinned Chrome for Testing
`150.0.7871.124`, an injected exact provider, or a complete exact-metrics cache.
Local package installation requires none of those browser binaries: fresh
labels can use the first-party local worker. This fallback is never packaged
into archive pages. [Measurement](measurement.md) records cache signatures and
unsupported-glyph diagnostics.

Preparation validates all requested view states before page writes. Output is
written into an adjacent staging directory and installed after successful asset
packaging. A write or validation failure retains the previous output. Cache
corruption causes checked recomputation; host times and machine names never
enter canonical geometry or published cache payloads.

No ordinary public page contains `laxLayout`, a browser layout library, a solver
or the custom search engine. The exact legacy implementation from the base
commit is retained only in `scripts/graph-legacy/` for development comparison.
The rollout is a source change on `graph-drawing`; reverting the migration
commits and rebuilding restores the previous renderer. The branch is not a
deployment authorization.

## Reproduction and metrics

`scripts/graph-inventory.mjs` extracts only the existing site's presentation
payloads, including all four concept ancestry/descendant states. Proof pages
currently contain judgment cards rather than a graph; this distinction is
recorded rather than inventing a baseline graph. Landing and submission proof
networks and submission dependencies are included.

The frozen corpus records renderer and database commits, per-page occurrences,
semantic payloads, graph kinds and a deterministic split. Algorithm diagnostics
and measurements are separate from geometry bytes. Geometry metrics distinguish
proper crossings, repeated crossing pairs, endpoint touches, tangencies,
positive-length overlaps, node/label/dock collisions, bends, length and extent.
Shared endpoints exempt only the common endpoint, never an entire edge pair.

Performance targets are evaluated on a declared reference host and fixture
tier. Per-graph regressions, cold/warm measurements, comparison limitations and
browser timing distributions belong to the run report. A passing unit suite
does not establish corpus quality or a universal resource bound.

## Methods

- [Gansner et al. (1993)](https://graphviz.org/documentation/TSE93.pdf): feasible tight-tree network simplex and auxiliary coordinate objective.
- [Barth et al. (2004)](https://jgaa.info/index.php/jgaa/article/view/paper88): bilayer inversion counting.
- [Matuszewski et al. (1999)](https://doi.org/10.1007/3-540-46648-7_22): layer sifting.
- [Brandes–Köpf](https://doi.org/10.1007/3-540-45848-4_3), with [both erratum corrections](https://arxiv.org/abs/2008.01252): alignment and compaction.
- [Wybrow et al.](https://doi.org/10.1007/978-3-642-11805-0_22): direction-aware orthogonal visibility routing.

External engines are optional development comparators only. The production
dependency graph must contain no third-party layout or solver runtime.
