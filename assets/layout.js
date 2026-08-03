// Deterministic Sugiyama-style layered DAG layout, shared by both site
// figures. Pure data-in/data-out: no DOM, no d3, so it is unit-testable in
// node. Layers are abstract indices growing upward from the sources; the
// caller converts them to pixels. Every stage breaks ties lexicographically
// and runs a fixed number of sweeps, so the same graph always yields the
// same drawing.
(() => {
  const VIRTUAL_WIDTH = 8;
  const ORDER_ROUNDS = 4;
  const POSITION_ROUNDS = 10;

  /** Longest-path layering from the sources, then a tightening pass that
   * lifts each source to sit directly below its first consumer instead of
   * stranding it at the bottom with a canvas-long edge. */
  function assignLayers(nodes, incoming, outgoing) {
    const layer = new Map();
    function getLayer(id) {
      if (layer.has(id)) return layer.get(id);
      layer.set(id, 0); // defensive guard: inputs are DAGs
      const dependencies = incoming.get(id) || [];
      const value = dependencies.length === 0 ? 0 : Math.max(...dependencies.map(getLayer)) + 1;
      layer.set(id, value);
      return value;
    }
    for (const node of nodes) getLayer(node.id);
    for (const node of nodes) {
      const consumers = outgoing.get(node.id) || [];
      if ((incoming.get(node.id) || []).length || !consumers.length) continue;
      layer.set(node.id, Math.min(...consumers.map((id) => layer.get(id))) - 1);
    }
    // A graph of only isolated sources keeps layer 0; lifted sources cannot
    // go below 0 because their consumers sit at layer >= 1.
    return layer;
  }

  /** Crossings between two adjacent layers, given segment endpoints as order
   * indices. O(n^2), fine at figure scale. */
  function countCrossingsBetween(segments) {
    let crossings = 0;
    for (let i = 0; i < segments.length; i += 1)
      for (let j = i + 1; j < segments.length; j += 1) {
        const a = segments[i];
        const b = segments[j];
        if ((a.lower - b.lower) * (a.upper - b.upper) < 0) crossings += 1;
      }
    return crossings;
  }

  function countCrossings(layers, position, segmentsByLayer) {
    let total = 0;
    for (let index = 0; index + 1 < layers.length; index += 1)
      total += countCrossingsBetween((segmentsByLayer[index] || []).map((segment) => ({
        lower: position.get(segment.lower),
        upper: position.get(segment.upper),
      })));
    return total;
  }

  function median(values) {
    if (!values.length) return null;
    const sorted = [...values].sort((a, b) => a - b);
    const mid = Math.floor(sorted.length / 2);
    return sorted.length % 2 ? sorted[mid] : (sorted[mid - 1] + sorted[mid]) / 2;
  }

  /** Weighted L2 isotonic regression: place ordered items at their desired
   * coordinates subject to minimum separations, by merging adjacent blocks
   * whose weighted means would otherwise invert. Optimal and deterministic. */
  function packOrdered(items) {
    // Work in gap-free coordinates: shift each item left by the sum of
    // separations before it, enforce plain monotonicity, then shift back.
    let shift = 0;
    const shifted = items.map((item, index) => {
      if (index > 0) shift += items[index - 1].sep;
      return { desired: item.desired - shift, weight: item.weight, shift };
    });
    const blocks = [];
    for (const item of shifted) {
      let block = { weightSum: item.weight, valueSum: item.weight * item.desired, count: 1 };
      while (blocks.length) {
        const previous = blocks[blocks.length - 1];
        if (previous.valueSum / previous.weightSum <= block.valueSum / block.weightSum) break;
        blocks.pop();
        block = {
          weightSum: previous.weightSum + block.weightSum,
          valueSum: previous.valueSum + block.valueSum,
          count: previous.count + block.count,
        };
      }
      blocks.push(block);
    }
    const result = [];
    let index = 0;
    for (const block of blocks) {
      const value = block.valueSum / block.weightSum;
      for (let member = 0; member < block.count; member += 1) {
        result.push(value + shifted[index].shift);
        index += 1;
      }
    }
    return result;
  }

  /**
   * Lay out a DAG. `nodes` carry `{ id, width }`; `edges` carry
   * `{ from, to }` with `from` strictly below `to`. Returns
   * `{ positions: Map<id, { x, layer }>, routes: [][], maxLayer, width }`
   * where `x` is a center coordinate in `[width/2, width - width/2]` and
   * `routes[i]` lists the via points `{ x, layer }` of `edges[i]` through
   * every intermediate layer (empty for adjacent-layer edges).
   */
  function layoutDag({ nodes, edges, nodeGap = 28 }) {
    if (!nodes.length) return { positions: new Map(), routes: [], maxLayer: 0, width: 0 };
    const incoming = new Map(nodes.map((node) => [node.id, []]));
    const outgoing = new Map(nodes.map((node) => [node.id, []]));
    for (const edge of edges) {
      incoming.get(edge.to).push(edge.from);
      outgoing.get(edge.from).push(edge.to);
    }
    const layerOf = assignLayers(nodes, incoming, outgoing);

    // Vertices = real nodes plus a chain of narrow virtual vertices for every
    // edge spanning more than one layer, so long edges claim horizontal space
    // in the layers they pass instead of cutting through boxes.
    const vertices = new Map();
    for (const node of nodes)
      vertices.set(node.id, { id: node.id, width: node.width, layer: layerOf.get(node.id), up: [], down: [], virtual: false });
    const routes = edges.map(() => []);
    const segments = [];
    edges.forEach((edge, index) => {
      let previous = edge.from;
      for (let layer = layerOf.get(edge.from) + 1; layer < layerOf.get(edge.to); layer += 1) {
        const id = `\0${index}@${layer}`;
        vertices.set(id, { id, width: VIRTUAL_WIDTH, layer, up: [], down: [], virtual: true });
        routes[index].push(id);
        segments.push({ lower: previous, upper: id });
        previous = id;
      }
      segments.push({ lower: previous, upper: edge.to });
    });
    for (const segment of segments) {
      vertices.get(segment.lower).up.push(segment.upper);
      vertices.get(segment.upper).down.push(segment.lower);
    }

    const maxLayer = Math.max(...[...layerOf.values()]);
    const layers = [];
    for (let index = 0; index <= maxLayer; index += 1) layers.push([]);
    for (const vertex of vertices.values()) layers[vertex.layer].push(vertex.id);
    for (const layer of layers) layer.sort();
    const segmentsByLayer = [];
    for (const segment of segments) {
      const index = vertices.get(segment.lower).layer;
      (segmentsByLayer[index] = segmentsByLayer[index] || []).push(segment);
    }

    // Ordering: alternating median sweeps, keeping the best ordering seen,
    // then adjacent transpositions while they strictly reduce crossings.
    const position = new Map();
    const reindex = () => layers.forEach((layer) => layer.forEach((id, index) => position.set(id, index)));
    reindex();
    const sortLayer = (layer, neighborsOf) => {
      const keys = new Map(layer.map((id) => {
        const key = median(neighborsOf(vertices.get(id)).map((neighbor) => position.get(neighbor)));
        return [id, key === null ? position.get(id) : key];
      }));
      layer.sort((a, b) => keys.get(a) - keys.get(b) || position.get(a) - position.get(b));
      layer.forEach((id, index) => position.set(id, index));
    };
    let best = layers.map((layer) => [...layer]);
    let bestCrossings = countCrossings(layers, position, segmentsByLayer);
    for (let round = 0; round < ORDER_ROUNDS; round += 1) {
      for (let index = 1; index <= maxLayer; index += 1) sortLayer(layers[index], (vertex) => vertex.down);
      for (let index = maxLayer - 1; index >= 0; index -= 1) sortLayer(layers[index], (vertex) => vertex.up);
      const crossings = countCrossings(layers, position, segmentsByLayer);
      if (crossings < bestCrossings) {
        bestCrossings = crossings;
        best = layers.map((layer) => [...layer]);
      }
    }
    best.forEach((layer, index) => { layers[index] = layer; });
    reindex();
    // Crossings around layer `index`: the pair below it plus the pair above
    // it, counted separately — inversions only mean crossings within one pair.
    const crossingsAround = (index) => {
      let total = 0;
      for (const pair of [segmentsByLayer[index - 1] || [], segmentsByLayer[index] || []])
        total += countCrossingsBetween(pair.map((segment) => ({
          lower: position.get(segment.lower), upper: position.get(segment.upper),
        })));
      return total;
    };
    for (let round = 0; round < ORDER_ROUNDS; round += 1) {
      let improved = false;
      for (let index = 0; index <= maxLayer; index += 1) {
        const layer = layers[index];
        for (let slot = 0; slot + 1 < layer.length; slot += 1) {
          const before = crossingsAround(index);
          [layer[slot], layer[slot + 1]] = [layer[slot + 1], layer[slot]];
          position.set(layer[slot], slot);
          position.set(layer[slot + 1], slot + 1);
          if (crossingsAround(index) < before) { improved = true; continue; }
          [layer[slot], layer[slot + 1]] = [layer[slot + 1], layer[slot]];
          position.set(layer[slot], slot);
          position.set(layer[slot + 1], slot + 1);
        }
      }
      if (!improved) break;
    }

    // Coordinates: pack each layer, then alternating sweeps of isotonic
    // regression toward the mean of the neighbors already swept over.
    // Virtual vertices weigh more, keeping long edges straight.
    const x = new Map();
    for (const layer of layers) {
      let cursor = 0;
      for (const id of layer) {
        const vertex = vertices.get(id);
        x.set(id, cursor + vertex.width / 2);
        cursor += vertex.width + nodeGap;
      }
    }
    const relaxLayer = (layer, neighborsOf) => {
      const items = layer.map((id, index) => {
        const vertex = vertices.get(id);
        const neighbors = neighborsOf(vertex).map((neighbor) => x.get(neighbor));
        const desired = neighbors.length
          ? neighbors.reduce((sum, value) => sum + value, 0) / neighbors.length
          : x.get(id);
        const weight = neighbors.length ? (vertex.virtual ? 8 : 1) : 0.001;
        const next = layer[index + 1];
        const sep = next
          ? vertex.width / 2 + vertices.get(next).width / 2 + nodeGap
          : 0;
        return { desired, weight, sep };
      });
      packOrdered(items).forEach((value, index) => x.set(layer[index], value));
    };
    for (let round = 0; round < POSITION_ROUNDS; round += 1) {
      for (let index = 1; index <= maxLayer; index += 1) relaxLayer(layers[index], (vertex) => vertex.down);
      for (let index = maxLayer - 1; index >= 0; index -= 1) relaxLayer(layers[index], (vertex) => vertex.up);
      for (let index = 0; index <= maxLayer; index += 1)
        relaxLayer(layers[index], (vertex) => [...vertex.down, ...vertex.up]);
    }

    let minEdge = Infinity;
    let maxEdge = -Infinity;
    for (const vertex of vertices.values()) {
      minEdge = Math.min(minEdge, x.get(vertex.id) - vertex.width / 2);
      maxEdge = Math.max(maxEdge, x.get(vertex.id) + vertex.width / 2);
    }
    const positions = new Map(nodes.map((node) => [node.id, {
      x: x.get(node.id) - minEdge,
      layer: layerOf.get(node.id),
    }]));
    return {
      positions,
      routes: routes.map((chain) => chain.map((id) => ({
        x: x.get(id) - minEdge,
        layer: vertices.get(id).layer,
      }))),
      maxLayer,
      width: maxEdge - minEdge,
    };
  }

  globalThis.laxLayout = { layoutDag };
})();
