import { countCrossings } from "./cross-count.js";
import type { OrderConstraint } from "./order-exact.js";
import type { Ordering, PortOrder, ProperGraph } from "./proper-graph.js";

/** Adjacent transpositions with free attachments reconsidered in the SAME
 * trial. Fixed-port scoring alone can mistake an uncrossing for a neutral
 * move that merely transfers the crossing to the preceding boundary.
 * Strict crossing descent prevents cycling. A completed unchanged sweep is
 * a local optimum only for these joint moves, never a global certificate. */
export function polishJointSwaps(graph: ProperGraph, input: Ordering, options: {
  trials: number; portSeparation: number; constraints: readonly OrderConstraint[];
  proposePorts: (layers: readonly (readonly number[])[], ports: PortOrder, affectedNodes: ReadonlySet<number>) => PortOrder;
}): { ordering: Ordering; trials: number; accepted: number; exhausted: boolean } {
  const layers = input.layers.map((row) => [...row]);
  let portOrder = input.portOrder, crossings = countCrossings(graph, layers, portOrder, options.portSeparation);
  let trials = 0, accepted = 0;
  const result = (exhausted: boolean) => ({ ordering: { layers, portOrder, crossings }, trials, accepted, exhausted });
  while (crossings > 0) {
    let improved = false;
    for (const row of layers) for (let i = 0; i + 1 < row.length; i++) {
      const u = row[i]!, v = row[i + 1]!;
      if (options.constraints.some(([a, b]) => a === u && b === v)) continue;
      if (trials >= options.trials) return result(true);
      trials++;
      // Only these nodes see changed opposite endpoint positions. Updating
      // unrelated free ports could mask a useful local move with another
      // simultaneous change. Include moved real nodes for parallel incidences.
      const affected = new Set<number>();
      for (const vertex of [u, v]) {
        const own = graph.vertices[vertex]!.nodeIndex;
        if (own !== undefined) affected.add(own);
        for (const s of [...graph.incoming[vertex]!, ...graph.outgoing[vertex]!]) {
          const segment = graph.segments[s]!;
          for (const endpoint of [segment.source, segment.target]) {
            const node = graph.vertices[endpoint]!.nodeIndex;
            if (node !== undefined) affected.add(node);
          }
        }
      }
      [row[i], row[i + 1]] = [v, u];
      const proposed = options.proposePorts(layers, portOrder, affected);
      // Score both neighboring boundaries and every changed attachment, not
      // just the crossing between the two moved vertices.
      const score = countCrossings(graph, layers, proposed, options.portSeparation);
      if (score < crossings) {
        portOrder = proposed; crossings = score; accepted++; improved = true;
      } else [row[i], row[i + 1]] = [u, v];
    }
    if (!improved) return result(false);
    // Revisit earlier pairs and neighboring ranks after accepted moves.
  }
  return result(false);
}
