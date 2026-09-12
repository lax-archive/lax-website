# Ranking and proper-layer ordering

These modules are first-party, DOM-free algorithms. Their input is the canonical,
permission-filtered `MeasuredGraph`; they do not read labels, navigation targets,
archive records, or browser state. Rank increases from a premise/dependency to
its user. Placement maps increasing ranks to decreasing screen y. No semantic
edge is reversed or removed here.

| Entry point | Contract |
| --- | --- |
| `indexedGraph(graph)` | Canonical node indexes and all edge incidences, with semantic IDs and port attachments retained in `graph`. |
| `weakComponents`, `stronglyConnectedComponents`, `topologicalOrder` | Integer endpoints; iterative traversals and CSR adjacency. SCC condensation retains each external edge separately and indexes internal incidences. |
| `rankGraph(graph, options)` | Node-indexed optimized and original feasible ranks, separate integer objectives, operation counts, checked termination status. |
| `rankIndexed(n, edges, options)` | Same solver on weighted DAG constraints; signed integer lower bounds support the coordinate auxiliary graph. |
| `makeProperGraph(graph, ranks, options)` | Real nodes occupy the first `graph.nodes.length` indexes; each dummy has its original edge index and chain offset. `chains[e]` includes both real endpoints. |
| `orderGraph(proper, options)` | At most four complete, distinct `Ordering` candidates and separate operation statistics. Invoke per weak component before packing. |
| `attachmentPositions`, `countCrossings` | Exact resolved port order at proper-layer boundaries; no geometry shortcut or center-only port estimate. |
| `subsetOrder`, `exactLayerOrder` | Exact fixed-neighbor pair-cost optimization, with explicit state budgets and hard prefix constraints. |

`ProperGraph` stores integer adjacency indexes, per-rank segment indexes, and
original-edge dummy chains. `Ordering` contains `layers`, `portOrder`, and a
recomputed proper crossing count. `portOrder` supplies preferences to the shared
`portOffsets` routine; that routine preserves fixed positions and the fixed-order
subsequence. Ordering and placement consequently evaluate the same attachments.
East/west terminal adapters and later route geometry still need independent
final-geometry validation.

## Feasible tight-tree rank assignment

The rank solver implements the feasible-tree network-simplex procedure in
[Gansner et al., section 2](https://graphviz.org/documentation/TSE93.pdf).
Longest paths supply a feasible initial ranking. A tight tree is grown within
each weak component by minimum-slack boundary shifts. Each pivot lengthens a
negative-cut tree edge until an opposite-cut edge becomes tight. Node objective
coefficients are accumulated over rooted subtrees to obtain cut values; DFS
intervals identify the affected subtree. This implementation rebuilds tree
metadata after a pivot instead of maintaining the paper's more intricate local
updates. It does not apply the optional balancing step.

`optimal-for-rank-objective` is returned only after all tree cuts have been
checked nonnegative. A depleted pivot budget returns `budget-exhausted`, with
feasible ranks. If the original feasible ranking has the better objective, the
capped result retains it. The original ranks remain separately available to the
geometry portfolio even after successful optimization. Nonunit minimum spans
are checked throughout; no source-tightening postpass modifies constraints.

Degeneracy uses [Bland's Rule I](https://people.ohio.edu/melkonia/math4620/bland.pdf).
View edge slacks as the nonnegative LP variables, eliminating potentials and
fixing one translation. Tight tree-edge slacks are nonbasic. The least canonical
edge with negative cut enters the slack basis, hence leaves the tree. Among
blocking basic slacks with minimum ratio (their derivative is -1), the least
canonical edge leaves the slack basis, hence enters the tree. Both tie rules
apply to zero-length pivots. Debug mode additionally detects repeated bases and
checks every edge constraint, tree tightness, and the independently recomputed
objective change after each pivot.

Ranks, weights, cuts and objectives use checked safe integers. Signed lower
bounds are accepted only by the indexed DAG API for the coordinate auxiliary
problem; semantic `MeasuredGraph` inputs require positive spans. The pivot
budget applies independently to each weak component. There is no wall-clock
branch in candidate selection.

## Proper layering and crossings

Before allocating dummy vertices, the implementation computes
`D = sum(rank(target) - rank(source) - 1)`. Expanded vertices, segments and rank
array sizes are checked against explicit operation-profile budgets. Exceeding
them produces `expansion-budget`; it does not publish a partial graph. Dummy
slots have positive width and collision-free private IDs. Parallel original
edges have separate chains. No sparse representation or sparse-backend
complexity bound is claimed.

The crossing counter follows the inversion reduction in
[Barth, Mutzel and Jünger, sections 2–3](https://jgaa.info/index.php/jgaa/article/download/paper88/2877/2684).
It uses coordinate compression and a Fenwick accumulator. Equal source
positions are queried together before insertion, and target prefix sums include
equality, so shared endpoints are excluded. Actual fixed-port x offsets and the
shared movable-port resolver determine boundary occurrences. Float64 integer
counters avoid 32-bit wraparound; additions and weighted products are checked
against safe-integer capacity. The quadratic test oracle shares neither the
accumulator nor its sorting/batching logic. This counter measures proper
boundary inversions; the final validator measures complete rendered routes.

## Ordering search and exact local scope

The four initial orders are canonical semantic order, its reverse, and two
fixed-seed permutations. Median and barycenter sweeps alternate directions.
Adjacent swaps and whole-vertex insertion trials score both neighboring
boundaries. The latter use the pair-cost update in
[Matuszewski, Schönfeld and Molitor, sections 3–4](https://wcms.itz.uni-halle.de/download.php?down=31862&elem=2717015).
Vertices are sifted by descending incidence degree and then the reverse
sequence, subject to a counted move budget. Sweeps can explore worse states;
the retained candidates are always complete orderings with recomputed total
crossing counts. Free-port reorderings are also explicit, whole-state trials.
The paper's empirical gains are not asserted for this implementation.

For a fixed layer and fixed neighbors/ports, `c(u,v)` counts the two-boundary
crossing contribution when u precedes v. The implemented recurrence appends v:

```
DP[S] = min_v (DP[S minus v] + sum_(u in S minus v) c(u,v))
```

Each unordered pair is charged once, when its rightmost member is appended.
Hard predecessor masks admit only feasible prefix subsets. Within-node terms
(including fixed-dock crossings) are constant in this node permutation and
remain in the final whole-graph score. Canonical local indexes and fixed
mask/vertex iteration determine ties. The direct implementation uses
`O(k² 2^k)` work and `O(2^k + k²)` memory; k is capped at 16, including dummies,
and the table is allocated only when its full size fits the state budget.

Wide-layer polishing uses contiguous windows of at most eight vertices.
Outside vertices remain on the same side of every moved vertex, making their
pair terms constant. This property would not hold for arbitrary noncontiguous
windows. An exhausted or oversized subproblem returns a feasible fallback with
an explicit status. A local optimum is never labeled a global ordering,
coordinate, or route optimum.

`order-chain.ts` proposes coherent moves of every internal dummy belonging to
one original long edge. Five relative gap positions are tried in deterministic
longest-chain order, under a 32-trial budget per restart. Every complete trial
is checked against hard layer orders and scored on all boundaries; only lower
crossings, or equal crossings with shorter attachment span, are accepted. The
separate gap metric counts dummy runs between real nodes, excluding outer
gutters. This is a bounded chain heuristic, not a sparse representation or a
guarantee about the gap objective.

`order-escape.ts` addresses local minima where a useful node move must accompany
a free-port reorder. After all restarts share their best complete states, it
enumerates a narrow layer only if its full factorial fits the unused move
budget of one restart. Each anchored order proposes outward barycenter orders,
refreshes free ports, and applies the existing exact DP to adjacent layers or
contiguous windows. Every state enters the same complete-ordering score and
must respect hard constraints. The escape is skipped when zero crossings are
already known. Permutation trials share the existing budget with sifting;
DP states/transitions, port trials and pair evaluations are counted separately.
No wall-clock branch or corpus-specific node identifier controls this search.

Before an exact neighbor DP, an optimistic node-pair bound can reject a trial
that cannot beat the current crossing count. It ignores within-node port
constraints and independently picks the cheaper orientation for each window
pair; outside-window relations remain constant. Ignoring constraints makes
this a lower bound even when free ports change afterward. The combined
permutation, barycenter and free-port search remains a heuristic. Only a
completed fixed-neighbor DP has the local exactness claim described above.

Crossings are the primary quick search score, then attachment span and canonical
ties. These scores prune ordering candidates only. They must not select a
production drawing without the independent validator and the versioned final
readability/extent policy. There is no claim of measured whole-corpus visual
improvement in these unit-test results.

## Independent checks

`test/graph-rank.test.ts` includes all 1,024 five-node DAGs under one fixed
topological labeling, compared with exhaustive unit-span rank assignments;
150 mixed-span/weight fixtures; 100 signed-bound auxiliary fixtures; and 300
degenerate/budget cases with per-pivot assertions. Additional cases cover
parallel constraints, diamonds, isolated vertices, nonunit paths, unsafe
integer arithmetic, and iterative 30,000-node chains/SCCs.

`test/graph-order.test.ts` checks 500 weighted/equal-endpoint boundary instances
against quadratic counting, counts beyond 32-bit range, fixed docks, both
neighboring boundaries, DP versus permutation enumeration through k=7, a full
k=16 solve, constrained contiguous windows, dummy-chain semantic round trips,
expansion diagnostics, paths/diamonds, dense unavoidable crossings, free versus
fixed port handling, deterministic input normalization, and search budgets.

`test/graph-chain.test.ts` checks complete-chain moves, identities, hard orders,
the trial cap, and the independent gap count. `test/graph-order-escape.test.ts`
retains two full measured tuning topologies and independent fixed-rank/free-port
oracles. The 15-node case enumerates 720 orders and 183,600 subset states to
establish one crossing; the 39-node case enumerates 2,880 source/twin-block
orders to establish nine. Every incidence remains in the oracle and emitted
geometry. The tests also enforce hard node/port orders and combined work caps.
These certificates apply to those fixed ranks and the protected layered route
family, not to all possible drawings or all rank assignments.

Run the focused checks with:

```sh
npm run build
npm test -- --run test/graph-rank.test.ts test/graph-order.test.ts test/graph-chain.test.ts test/graph-order-escape.test.ts
```

The source methods above were read before implementing their corresponding
algorithms. The sifting preprint's PDF text encoding is damaged; its method and
experimental pages were read as rendered page images. The code is original;
no upstream layout implementation or solver package is imported.
