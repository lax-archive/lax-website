import { attachmentPositions, countCrossings } from "./cross-count.js";
import type { OrderConstraint } from "./order-exact.js";
import type { Ordering, ProperGraph } from "./proper-graph.js";
import { compareText } from "./normalize.js";

/** Coherent dummy-chain proposals. Each trial moves every interior dummy of
 * ONE original long edge to corresponding relative gaps, then scores every
 * affected boundary as a complete ordering. This is a bounded heuristic,
 * distinct from a sparse long-edge representation or a gap theorem. */
export function polishChains(graph: ProperGraph, input: Ordering, options: {
  moves?: number; portSeparation?: number; constraints?: readonly OrderConstraint[];
} = {}): { ordering: Ordering; moves: number; gaps: number } {
  const limit = options.moves ?? 32, separation = options.portSeparation ?? 8;
  const score = (layers: readonly (readonly number[])[]) => {
    const positions = attachmentPositions(graph, layers, input.portOrder, separation);
    return [countCrossings(graph, layers, input.portOrder, separation),
      graph.segments.reduce((sum, _, i) => sum + Math.abs(positions.source[i]! - positions.target[i]!), 0)];
  };
  let layers = input.layers.map((row) => [...row]), best = score(layers), moves = 0;
  const chains = graph.chains.map((chain, edge) => ({ chain, edge })).filter(({ chain }) => chain.length > 3)
    .sort((a, b) => b.chain.length - a.chain.length || compareText(graph.source.edges[a.edge]!.id, graph.source.edges[b.edge]!.id));
  for (const { chain } of chains) for (const fraction of [.5, .25, .75, 0, 1]) {
    if (moves >= limit) break;
    moves++;
    const trial = layers.map((row) => [...row]);
    for (const vertex of chain.slice(1, -1)) {
      const row = trial[graph.vertices[vertex]!.rank]!, index = row.indexOf(vertex);
      row.splice(index, 1); row.splice(Math.round(fraction * row.length), 0, vertex);
    }
    if (options.constraints?.some(([u, v]) => {
      const row = trial[graph.vertices[u]!.rank]!;
      return row.indexOf(u) >= row.indexOf(v);
    })) continue;
    const quality = score(trial);
    if (quality[0]! < best[0]! || quality[0] === best[0] && quality[1]! < best[1]!) { layers = trial; best = quality; }
  }
  return { ordering: { layers, portOrder: input.portOrder, crossings: best[0]! }, moves, gaps: dummyGaps(graph, layers) };
}

/** Number of nonempty dummy runs BETWEEN real nodes, excluding outer gutters. */
export function dummyGaps(graph: ProperGraph, layers: readonly (readonly number[])[]): number {
  let gaps = 0;
  for (const row of layers) {
    let real = false, dummy = false;
    for (const vertex of row) {
      if (graph.vertices[vertex]!.nodeIndex === undefined) { if (real) dummy = true; }
      else { if (real && dummy) gaps++; real = true; dummy = false; }
    }
  }
  return gaps;
}
