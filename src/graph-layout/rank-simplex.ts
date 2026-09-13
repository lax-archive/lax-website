import { adjacency, indexedGraph, topologicalOrder, weakComponents } from "./components.js";
import { compareText } from "./normalize.js";
import { GraphDiagnosticError, type MeasuredGraph } from "./types.js";

export type RankEdge = Readonly<{ id: string; source: number; target: number; minRankSpan: number; weight?: number }>;
export type RankTermination = "optimal-for-rank-objective" | "budget-exhausted";
export type RankOptions = Readonly<{
  pivotBudget?: number; debug?: boolean;
  /** Debug-only observer: ranks/tree use LOCAL component indexes. */
  onPivot?: (state: Readonly<{ ranks: readonly number[]; edges: readonly RankEdge[]; treeEdgeIndexes: readonly number[]; objective: number; delta: number }>) => void;
}>;
export type RankResult = Readonly<{
  ranks: readonly number[]; initialRanks: readonly number[];
  objective: number; initialObjective: number; termination: RankTermination;
  pivots: number; zeroPivots: number; feasibleTreeShifts: number;
  componentTerminations: readonly RankTermination[];
}>;

function checked(value: number, what: string): number {
  if (!Number.isSafeInteger(value)) throw new GraphDiagnosticError([{ code: "rank-arithmetic", message: `Exact integer capacity exceeded in ${what}` }]);
  return value;
}
export function rankObjective(edges: readonly RankEdge[], ranks: readonly number[]): number {
  let value = 0;
  for (const edge of edges) value = checked(value + checked((edge.weight ?? 1) * checked(ranks[edge.target]! - ranks[edge.source]!, "edge span"), "weighted span"), "rank objective");
  return value;
}
export function assertFeasibleRanks(nodeCount: number, edges: readonly RankEdge[], ranks: readonly number[]): void {
  if (ranks.length !== nodeCount || ranks.some((rank) => !Number.isSafeInteger(rank)))
    throw new GraphDiagnosticError([{ code: "rank-feasibility", message: "Ranking must supply a safe integer for each vertex" }]);
  for (const edge of edges) if (checked(ranks[edge.target]! - ranks[edge.source]!, "feasibility span") < edge.minRankSpan)
    throw new GraphDiagnosticError([{ code: "rank-feasibility", message: "Ranking violates an edge's minimum span", ids: [edge.id] }]);
}
export function longestPathRanks(nodeCount: number, edges: readonly RankEdge[]): number[] {
  const order = topologicalOrder(nodeCount, edges), { offsets, edgeIndexes } = adjacency(nodeCount, edges, "outgoing"), ranks = new Array<number>(nodeCount).fill(0);
  for (const u of order) for (let at = offsets[u]!; at < offsets[u + 1]!; at++) {
    const edge = edges[edgeIndexes[at]!]!;
    ranks[edge.target] = Math.max(ranks[edge.target]!, checked(ranks[u]! + edge.minRankSpan, "longest-path ranking"));
  }
  return ranks;
}

type TreeInfo = { parent: Int32Array; parentEdge: Int32Array; enter: Int32Array; leave: Int32Array; cuts: number[] };
/** Rooted tight tree with DFS intervals and bottom-up objective-coefficient
 * sums. Cut metadata is rebuilt after exchanges in O(n+m), rather than using
 * the paper's more intricate path-only updates. */
function treeInfo(nodeCount: number, edges: readonly RankEdge[], tree: ReadonlySet<number>): TreeInfo {
  const treeEdges = [...tree].sort((a, b) => a - b), treeArcs = treeEdges.map((e) => edges[e]!);
  const links = adjacency(nodeCount, treeArcs, "undirected");
  const parent = new Int32Array(nodeCount).fill(-1), parentEdge = new Int32Array(nodeCount).fill(-1);
  const enter = new Int32Array(nodeCount), leave = new Int32Array(nodeCount), order: number[] = [], stack = [0], cursors = [links.offsets[0]!];
  parent[0] = 0; enter[0] = 0; let clock = 1;
  while (stack.length) {
    const top = stack.length - 1, v = stack[top]!, at = cursors[top]!;
    if (at === links.offsets[v + 1]!) { leave[v] = clock; order.push(v); stack.pop(); cursors.pop(); continue; }
    cursors[top] = at + 1; const w = links.neighbors[at]!;
    if (w === parent[v]) continue;
    if (parent[w] !== -1) throw new Error("Internal rank basis is not a tree");
    parent[w] = v; parentEdge[w] = treeEdges[links.edgeIndexes[at]!]!; enter[w] = clock++;
    stack.push(w); cursors.push(links.offsets[w]!);
  }
  if (clock !== nodeCount) throw new Error("Internal rank basis does not span its component");
  const balance = new Array<number>(nodeCount).fill(0), cuts = new Array<number>(edges.length).fill(0);
  for (const edge of edges) {
    const weight = edge.weight ?? 1;
    balance[edge.source] = checked(balance[edge.source]! - weight, "node objective coefficient");
    balance[edge.target] = checked(balance[edge.target]! + weight, "node objective coefficient");
  }
  for (const v of order) if (v !== 0) {
    const e = parentEdge[v]!, edge = edges[e]!;
    cuts[e] = edge.target === v ? balance[v]! : -balance[v]!;
    balance[parent[v]!] = checked(balance[parent[v]!]! + balance[v]!, "tree cut sum");
  }
  return { parent, parentEdge, enter, leave, cuts };
}

function solveComponent(nodeCount: number, edges: readonly RankEdge[], start: readonly number[], options: RankOptions, budget: number) {
  const ranks = [...start], tree = new Set<number>();
  const incident = adjacency(nodeCount, edges, "undirected"), inside = new Uint8Array(nodeCount); inside[0] = 1;
  let visited = 1, feasibleTreeShifts = 0, pivots = 0, zeroPivots = 0;
  const slack = (edge: RankEdge) => checked(checked(ranks[edge.target]! - ranks[edge.source]!, "slack span") - edge.minRankSpan, "slack");
  const grow = (seeds: number[]) => {
    for (let cursor = 0; cursor < seeds.length; cursor++) {
      const v = seeds[cursor]!;
      for (let at = incident.offsets[v]!; at < incident.offsets[v + 1]!; at++) {
        const e = incident.edgeIndexes[at]!, w = incident.neighbors[at]!;
        if (!inside[w] && slack(edges[e]!) === 0) { inside[w] = 1; visited++; tree.add(e); seeds.push(w); }
      }
    }
  };
  grow([0]);
  while (visited < nodeCount) {
    let selected = -1, minimum = Infinity;
    for (let e = 0; e < edges.length; e++) {
      const edge = edges[e]!;
      if (inside[edge.source] === inside[edge.target]) continue;
      const candidate = slack(edge);
      if (candidate < minimum) { minimum = candidate; selected = e; }
    }
    if (selected < 0) throw new Error("Disconnected graph passed to rank component solver");
    const edge = edges[selected]!, delta = inside[edge.source] ? minimum : -minimum;
    for (let v = 0; v < nodeCount; v++) if (inside[v]) ranks[v] = checked(ranks[v]! + delta, "feasible-tree shift");
    feasibleTreeShifts++;
    const next = inside[edge.source] ? edge.target : edge.source; inside[next] = 1; visited++; tree.add(selected); grow([next]);
    if (options.debug) assertFeasibleRanks(nodeCount, edges, ranks);
  }
  let termination: RankTermination = "optimal-for-rank-objective";
  const seenBases = options.debug ? new Set<string>() : undefined;
  while (true) {
    const info = treeInfo(nodeCount, edges, tree);
    if (options.debug) {
      const key = [...tree].sort((a, b) => a - b).join(",");
      if (seenBases!.has(key)) throw new Error("Bland pivot policy revisited a rank basis");
      seenBases!.add(key);
      assertFeasibleRanks(nodeCount, edges, ranks);
      for (const e of tree) if (slack(edges[e]!) !== 0) throw new Error("Rank basis contains a nontight edge");
    }
    // Bland's rule in the slack-variable primal: the least-index improving
    // nonbasic slack (a tight tree edge) enters. This is a tree LEAVE edge.
    let leaving = -1;
    for (let e = 0; e < edges.length; e++) if (tree.has(e) && info.cuts[e]! < 0) { leaving = e; break; }
    if (leaving === -1) break; // Only this checked cut condition certifies rank optimality.
    if (pivots >= budget) { termination = "budget-exhausted"; break; }
    const leaveEdge = edges[leaving]!;
    const child = info.parentEdge[leaveEdge.target] === leaving ? leaveEdge.target : leaveEdge.source;
    const headIsSubtree = child === leaveEdge.target;
    const inSubtree = (v: number) => info.enter[v]! >= info.enter[child]! && info.enter[v]! < info.leave[child]!;
    const inHead = (v: number) => inSubtree(v) === headIsSubtree;
    let entering = -1, delta = Infinity;
    for (let e = 0; e < edges.length; e++) {
      const edge = edges[e]!;
      if (!inHead(edge.source) || inHead(edge.target)) continue;
      const candidate = slack(edge);
      // All decreasing slacks have derivative -1, so the ratio test is
      // simply min slack. Least edge index breaks ties (Bland's leaving
      // BASIC slack), including zero-length degenerate pivots.
      if (candidate < delta) { delta = candidate; entering = e; }
    }
    if (entering < 0) throw new GraphDiagnosticError([{ code: "rank-unbounded", message: "Negative cut has no blocking edge; check edge weights", ids: [leaveEdge.id] }]);
    const oldObjective = options.debug ? rankObjective(edges, ranks) : 0;
    for (let v = 0; v < nodeCount; v++) if (inSubtree(v)) ranks[v] = checked(ranks[v]! + (headIsSubtree ? delta : -delta), "simplex pivot");
    tree.delete(leaving); tree.add(entering); pivots++; if (!delta) zeroPivots++;
    if (options.debug) {
      assertFeasibleRanks(nodeCount, edges, ranks);
      if (rankObjective(edges, ranks) !== oldObjective + checked(info.cuts[leaving]! * delta, "pivot objective delta")) throw new Error("Rank pivot objective disagrees with cut derivative");
    }
    options.onPivot?.({ ranks: [...ranks], edges, treeEdgeIndexes: [...tree].sort((a, b) => a - b), objective: rankObjective(edges, ranks), delta });
  }
  // A capped feasible-tree search must not discard a better original feasible
  // ranking. Both candidates still remain available to the geometry portfolio.
  const selected = termination === "budget-exhausted" && rankObjective(edges, start) < rankObjective(edges, ranks) ? [...start] : ranks;
  let minimum = Infinity; for (const rank of selected) minimum = Math.min(minimum, rank);
  for (let v = 0; v < selected.length; v++) selected[v] = checked(selected[v]! - minimum, "rank normalization");
  assertFeasibleRanks(nodeCount, edges, selected);
  return { ranks: selected, termination, pivots, zeroPivots, feasibleTreeShifts };
}

/** Signed integer bounds support the auxiliary DAG for fixed-order L1
 * coordinates. Public semantic rankGraph inputs retain positive min spans.
 * Every weak component is solved independently; pivotBudget is PER component,
 * so adding an isolated component cannot consume another's search budget. */
export function rankIndexed(nodeCount: number, inputEdges: readonly RankEdge[], options: RankOptions = {}): RankResult {
  const pivotBudget = options.pivotBudget ?? 4096;
  if (!Number.isSafeInteger(pivotBudget) || pivotBudget < 0) throw new GraphDiagnosticError([{ code: "rank-budget", message: "Pivot budget must be a nonnegative safe integer" }]);
  const ids = new Set<string>();
  for (const edge of inputEdges) {
    if (!edge.id || ids.has(edge.id)) throw new GraphDiagnosticError([{ code: "rank-edge-id", message: "Rank edges require unique stable IDs", ids: [edge.id] }]);
    ids.add(edge.id);
    if (!Number.isSafeInteger(edge.minRankSpan) || !Number.isSafeInteger(edge.weight ?? 1) || (edge.weight ?? 1) < 0)
      throw new GraphDiagnosticError([{ code: "rank-constraint", message: "Rank bounds must be safe integers and weights nonnegative safe integers", ids: [edge.id] }]);
  }
  const edges = [...inputEdges].sort((a, b) => compareText(a.id, b.id));
  const initialRanks = longestPathRanks(nodeCount, edges), ranks = [...initialRanks];
  const components = weakComponents(nodeCount, edges), componentOf = new Int32Array(nodeCount), localIndex = new Int32Array(nodeCount);
  components.forEach((members, component) => members.forEach((v, index) => { componentOf[v] = component; localIndex[v] = index; }));
  const componentEdges: RankEdge[][] = components.map(() => []);
  for (const edge of edges) componentEdges[componentOf[edge.source]!]!.push({ ...edge, source: localIndex[edge.source]!, target: localIndex[edge.target]! });
  let pivots = 0, zeroPivots = 0, feasibleTreeShifts = 0;
  const componentTerminations: RankTermination[] = [];
  components.forEach((members, component) => {
    const result = solveComponent(members.length, componentEdges[component]!, members.map((v) => initialRanks[v]!), options, pivotBudget);
    members.forEach((v, index) => { ranks[v] = result.ranks[index]!; });
    pivots += result.pivots; zeroPivots += result.zeroPivots; feasibleTreeShifts += result.feasibleTreeShifts;
    componentTerminations.push(result.termination);
  });
  assertFeasibleRanks(nodeCount, edges, ranks);
  return { ranks, initialRanks, objective: rankObjective(edges, ranks), initialObjective: rankObjective(edges, initialRanks),
    termination: componentTerminations.includes("budget-exhausted") ? "budget-exhausted" : "optimal-for-rank-objective",
    pivots, zeroPivots, feasibleTreeShifts, componentTerminations };
}
export function rankGraph(graph: MeasuredGraph, options: RankOptions = {}): RankResult {
  const indexed = indexedGraph(graph); return rankIndexed(indexed.nodeCount, indexed.edges, options);
}
