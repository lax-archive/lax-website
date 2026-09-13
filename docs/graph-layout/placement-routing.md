# Placement and routing

The production core uses measured node envelopes and node-local port offsets.
All coordinates here are SVG coordinates; node positions are top-left corners,
proper-vertex horizontal coordinates are centers, and semantic rank increases
upward. These modules contain no browser, filesystem, network, or third-party
layout dependency.

## Port finalization

`ports.ts` finalizes attachment positions before either crossing scoring or
coordinates. Fixed positions are copied exactly. Fixed-order attachments keep
their constrained subsequence while free-order preferences may interleave.
Adjustable positions reserve the configured separation, avoid fixed attachment
positions, and fail with `port-capacity` when the measured side cannot fit them.
The renderer consumes the resulting positions and does not choose ports again.

## Corrected Brandes–Köpf placement

`coordinates-bk.ts` implements median-neighbor vertical alignment, four
directional compactions, and the average-median balanced combination. It reads
the original [Brandes–Köpf method](https://kim246.wwwdns.kim.uni-konstanz.de/publications/bk-fshca-01.pdf)
together with the [Brandes–Walter–Zink erratum](https://arxiv.org/abs/2008.01252).

Both erratum corrections are explicit. First, immutable block-relative
coordinates are copied to every member before applying any class offset.
Second, the class DAG is constructed in full, then offsets propagate in
dependency order. A class therefore consumes the final shift of every class
that constrains it. The implementation uses iterative DAG passes rather than
recursive `place_block` calls or a traversal-order-dependent root exception.

The two regression tests use three interacting classes. Omitting accumulation
places two distinct boxes together; reusing an already shifted root moves an
aligned member twice. Separate tests cover both failures.

Size and port support are explicit extensions. A block member carries a
potential relative to its root so an aligned pair shares the x coordinate of
its *attachments*, including unequal measured fixed offsets. Compaction
constraints include the two half-widths, the configured clearance, and the
difference of these potentials. Every directional pass and the balanced result
is checked against every same-layer separation constraint.

Type-1 conflicts favor the inner dummy segment. Both inner segments in a type-2
conflict are made unavailable for alignment; their order is preserved.
Prefix/suffix extrema detect these conflicts without enumerating every pair.
Conflicting alignments never justify moving a node independently of its ports.

## Fixed-order L1 candidate

`coordinates-l1.ts` uses the auxiliary-graph construction in
[Gansner et al.](https://graphviz.org/documentation/TSE93.pdf). For a proper
segment with attached horizontal coordinates `x(u)+a` and `x(v)+b`, an auxiliary
source `z` has constraints `x(u)-z >= -a` and `x(v)-z >= -b`, both weight one.
At the optimum, the auxiliary source reaches the smaller attached coordinate;
the objective differs from the absolute endpoint difference by a constant.
Same-layer separation arcs have weight zero and hard minimum length. The
network simplex implementation accepts these signed lower bounds. Coordinates
use the published 0.001px grid, with minimum separations rounded upward.

The result reports the simplex termination condition and pivot count. A
budget-exhausted solution remains feasible and is not called optimal. Even a
completed solve only optimizes this fixed-order horizontal objective. Tiny
independent integer enumeration tests verify the objective with unequal port
offsets.

## Protected baseline routes

`corridors.ts` assigns a complete envelope to each row. A long edge's dummy owns
a positive-width slot through every intermediate row; transitions occur only
inside empty inter-row bands. Real endpoints keep their specified normals.
North-source and south-target endpoints have at least 12px escape space,
including the arrowhead's exclusion region. Other fixed directions use explicit
terminal-adapter sections confined to the node's documented 24px neighborhood.

Band height includes measured row heights, two escape regions, and channel
capacity. The initial capacity bound reserves one horizontal channel per
incidence in that band. `bandExpansion` permits a bounded caller to request
more room without changing attachments. This is deliberately conservative;
the full-corpus selection report must disclose its height cost.

No node-clear shortcut exists in this path. Simplification operates on the
published 0.001px coordinate grid and removes only a collinear point lying
between its neighbors. This retains terminal stubs when a nearly collinear
unquantized connector rounds onto two distinct grid lines. Half-grid ties
within two relative machine epsilons use a consistent toward-positive-infinity
rule, so equivalent center/width arithmetic cannot split an aligned attachment.
The geometric validator's normal and clearance tolerances are unchanged. Every
semantic edge retains its identity, connected route sections, and terminal
target port.

## Orthogonal candidate

`orthogonal-route.ts` follows the visibility-graph and direction-state search
methods in [Wybrow–Marriott–Stuckey](https://users.monash.edu/~mwybrow/papers/wybrow-gd-2009.pdf).
Interesting points cast horizontal and vertical obstacle-clipped visibility
rays. Their visible intersections form the graph; consecutive visible vertices
are connected. Search state includes the incoming cardinal direction, and the
Manhattan heuristic ignores nonnegative bend and crossing costs. Tests compare
the result with an independent unit-grid Bellman–Ford oracle.

Lax restricts ordinary routes to their allocated rank bands. It constructs no
whole-drawing x-by-y grid. Stable edge orders, crossing penalties, and reserved
parallel tracks are Lax's bounded multi-edge heuristics; the paper's
single-connector optimality is not a global drawing guarantee. Coincident runs
are unavailable search transitions. Exhausted or failed searches discard the
entire alternative while leaving the protected baseline available.

Up to two original edges with the highest crossing pressure are ripped up after
a complete pass. A replacement is accepted only after the complete graph is
reassembled, quantized, and independently validated and improves the fixed
tuple of crossings, repeated-crossing pairs, tangencies, bends, then length.
The default routine returns at most one best valid geometry for each stable
processing order. It reports search expansions and visibility-vertex counts
separately from canonical geometry. The caller controls the number of orders
and rip-up moves.

## Final curves and validation

`route-refine.ts` first checks the complete polyline drawing. Corner cuts are
clamped to half of each adjacent segment and retain 10px terminal approaches.
At most three decreasing radii are tried. Every candidate is serialized at the
actual SVG precision, parsed, quantized, and checked by the independent
validator. Curve flattening uses its adaptive deviation bound. An invalid
rounding or one that adds crossings, repeated crossing pairs, or tangencies
is rejected; the validated polyline is returned unchanged.

The validator checks both the reference corridor and emitted commands. Exact
quadratic derivatives enforce upward flow and exact command tangents preserve
straight arrow approaches even below flattening tolerance. Display groups need
independently verified SCC membership and one identified boundary gate per
external incidence, joined by explicit route sections. Unrelated group
intrusions, self-intersections, misplaced markers, and arrowhead collisions with
nodes, labels, docks, or other heads are hard defects. Bend metrics count each
geometric corner or quadratic once, independently of tessellation density.

`test/graph-coordinates.test.ts` and `test/graph-routing.test.ts` exercise the
algorithm oracles, both compaction defects, inner conflicts, fixed positions,
unequal widths, capacity diagnostics, easy path/diamond drawings, long skip
edges, dense unavoidable crossings, high-degree ports, empty graphs, and all
five BK candidates over forty deterministic varied-width DAGs. Corpus quality,
runtime, transfer size, and browser behavior are measured by the site-wide
integration reports; these unit tests do not establish those performance goals.
