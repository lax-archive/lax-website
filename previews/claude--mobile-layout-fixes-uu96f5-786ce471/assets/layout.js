// Deterministic Sugiyama-style layered layout, shared by all site graphs.
// The phases are: rank assignment; proper layering with one dummy vertex per
// traversed rank; crossing reduction by alternating median/barycenter sweeps,
// deterministic restarts, and whole-vertex sifting; repeated-crossing removal;
// and constrained horizontal coordinate assignment biased toward straight
// dummy chains.
//
// Layers grow upward from the sources. The module is pure data-in/data-out and
// deliberately dependency-free so the same code runs in browsers and tests.
(() => {
  const VIRTUAL_WIDTH = 2;
  const ORDER_ROUNDS = 5;
  const SIFT_ROUNDS = 1;
  const POSITION_ROUNDS = 28;
  const FULL_SEARCH_NODE_LIMIT = 64;
  const FULL_SEARCH_VERTEX_LIMIT = 200;
  const FULL_SEARCH_SEGMENT_LIMIT = 300;

  const compareScore = (a, b) => a.crossings - b.crossings || a.span - b.span;
  const compareText = (a, b) => a < b ? -1 : a > b ? 1 : 0;

  /** Longest-path ranks, followed by the safe source-tightening used by the
   * original renderer: a source sits immediately below its first consumer. */
  function assignLayers(nodes, incoming, outgoing) {
    const layer = new Map();
    function getLayer(id) {
      if (layer.has(id)) return layer.get(id);
      layer.set(id, 0); // defensive recursion guard; callers provide DAGs
      const dependencies = incoming.get(id) || [];
      const value = dependencies.length === 0
        ? 0
        : Math.max(...dependencies.map(getLayer)) + 1;
      layer.set(id, value);
      return value;
    }
    for (const node of nodes) getLayer(node.id);
    for (const node of nodes) {
      const consumers = outgoing.get(node.id) || [];
      if ((incoming.get(node.id) || []).length || !consumers.length) continue;
      layer.set(node.id, Math.min(...consumers.map((id) => layer.get(id))) - 1);
    }
    return layer;
  }

  function median(values) {
    if (!values.length) return null;
    const sorted = [...values].sort((a, b) => a - b);
    const middle = Math.floor(sorted.length / 2);
    return sorted.length % 2
      ? sorted[middle]
      : (sorted[middle - 1] + sorted[middle]) / 2;
  }

  function barycenter(values) {
    if (!values.length) return null;
    return values.reduce((sum, value) => sum + value, 0) / values.length;
  }

  function countCrossingsBetween(segments, position) {
    if (segments.length < 2) return 0;
    const ordered = segments.map((segment) => ({
      lower: position.get(segment.lower),
      upper: position.get(segment.upper),
    })).sort((a, b) => a.lower - b.lower || a.upper - b.upper);
    const largestUpper = ordered.reduce((largest, segment) =>
      Math.max(largest, segment.upper), 0);
    const tree = new Uint32Array(largestUpper + 2);
    const prefixCount = (slot) => {
      let total = 0;
      for (let index = slot; index > 0; index -= index & -index)
        total += tree[index];
      return total;
    };
    const add = (slot) => {
      for (let index = slot; index < tree.length; index += index & -index)
        tree[index] += 1;
    };

    // Segments with the same lower endpoint are queried before any of them
    // enter the tree, so a shared endpoint never counts as a crossing. The
    // Fenwick tree then counts only earlier upper endpoints strictly to the
    // right of the current one.
    let crossings = 0;
    let seen = 0;
    for (let first = 0; first < ordered.length;) {
      let after = first + 1;
      while (after < ordered.length && ordered[after].lower === ordered[first].lower)
        after += 1;
      for (let index = first; index < after; index += 1)
        crossings += seen - prefixCount(ordered[index].upper + 1);
      for (let index = first; index < after; index += 1) {
        add(ordered[index].upper + 1);
        seen += 1;
      }
      first = after;
    }
    return crossings;
  }

  function crossingCount(segmentsByLayer, position) {
    return segmentsByLayer.reduce((total, segments) =>
      total + countCrossingsBetween(segments || [], position), 0);
  }

  /** A crossing-neutral secondary objective. Short spans tend to produce
   * shorter edges and fewer visually necessary bends. */
  function spanScore(segments, position) {
    return segments.reduce((total, segment) =>
      total + Math.abs(position.get(segment.lower) - position.get(segment.upper)), 0);
  }

  const cloneLayers = (layers) => layers.map((layer) => [...layer]);

  /** A fixed-seed shuffle supplies reproducible restarts without making the
   * result depend on object iteration order or browser randomness. */
  function shuffledLayers(layers, seed) {
    let state = seed >>> 0;
    const next = () => {
      state ^= state << 13;
      state ^= state >>> 17;
      state ^= state << 5;
      return state >>> 0;
    };
    return layers.map((source) => {
      const layer = [...source];
      for (let index = layer.length - 1; index > 0; index -= 1) {
        const other = next() % (index + 1);
        [layer[index], layer[other]] = [layer[other], layer[index]];
      }
      return layer;
    });
  }

  function positionsOf(layers) {
    const position = new Map();
    layers.forEach((layer) => layer.forEach((id, index) => position.set(id, index)));
    return position;
  }

  function stateScore(segments, segmentsByLayer, position) {
    return {
      crossings: crossingCount(segmentsByLayer, position),
      span: spanScore(segments, position),
    };
  }

  /** One deterministic sweep/sifting search. Keeping the best
   * complete state seen makes exploratory sweeps safe: no returned ordering
   * has more crossings than its seed. */
  function optimizeOrdering(seed, vertices, segments, segmentsByLayer, startUpward, centerOf) {
    const layers = cloneLayers(seed);
    const position = positionsOf(layers);
    let bestLayers = cloneLayers(layers);
    let bestScore = stateScore(segments, segmentsByLayer, position);

    const reindex = (layerIndex) => {
      layers[layerIndex].forEach((id, index) => position.set(id, index));
    };
    const consider = () => {
      const score = stateScore(segments, segmentsByLayer, position);
      if (compareScore(score, bestScore) < 0) {
        bestScore = score;
        bestLayers = cloneLayers(layers);
      }
    };
    const sortLayer = (layerIndex, neighborsOf) => {
      const layer = layers[layerIndex];
      const oldPosition = new Map(layer.map((id, index) => [id, index]));
      const keys = new Map(layer.map((id) => {
        const neighbors = neighborsOf(vertices.get(id));
        const key = centerOf(neighbors.map((neighbor) => position.get(neighbor)));
        return [id, key === null ? oldPosition.get(id) : key];
      }));
      layer.sort((a, b) => keys.get(a) - keys.get(b) ||
        oldPosition.get(a) - oldPosition.get(b) || compareText(a, b));
      reindex(layerIndex);
    };
    /** Move each vertex directly to its best slot instead of requiring every
     * intermediate adjacent swap to improve. This escapes the common local
     * minimum in which a useful insertion temporarily raises the crossing
     * count. Pairwise crossing costs and incremental span deltas keep a
     * complete slot scan linear in rank size for bounded-degree graphs. */
    const siftLayer = (layerIndex, reverseTies) => {
      const layer = layers[layerIndex];
      if (layer.length < 2) return false;
      const pairCost = new Map();
      const crossingCost = (firstId, secondId) => {
        const key = `${firstId}\u0001${secondId}`;
        if (pairCost.has(key)) return pairCost.get(key);
        const first = vertices.get(firstId);
        const second = vertices.get(secondId);
        let cost = 0;
        for (const side of ['down', 'up'])
          for (const firstNeighbor of first[side])
            for (const secondNeighbor of second[side])
              if (position.get(firstNeighbor) > position.get(secondNeighbor)) cost += 1;
        pairCost.set(key, cost);
        return cost;
      };
      const visit = [...layer].sort((a, b) => {
        const firstDegree = vertices.get(a).down.length + vertices.get(a).up.length;
        const secondDegree = vertices.get(b).down.length + vertices.get(b).up.length;
        return secondDegree - firstDegree || (reverseTies ? compareText(b, a) : compareText(a, b));
      });
      let anyChange = false;

      for (const id of visit) {
        const currentSlot = layer.indexOf(id);
        const others = layer.filter((candidate) => candidate !== id);
        const crossingBySlot = [];
        let crossing = others.reduce((total, other) => total + crossingCost(id, other), 0);
        crossingBySlot.push(crossing);
        const spanBySlot = [0];
        let span = 0;
        const incidentSpan = (vertexId, slot) => {
          const vertex = vertices.get(vertexId);
          let total = 0;
          for (const neighbor of vertex.down)
            total += Math.abs(slot - position.get(neighbor));
          for (const neighbor of vertex.up)
            total += Math.abs(slot - position.get(neighbor));
          return total;
        };
        for (let slot = 0; slot < others.length; slot += 1) {
          const other = others[slot];
          crossing += crossingCost(other, id) - crossingCost(id, other);
          crossingBySlot.push(crossing);
          span += incidentSpan(id, slot + 1) - incidentSpan(id, slot) +
            incidentSpan(other, slot) - incidentSpan(other, slot + 1);
          spanBySlot.push(span);
        }

        let bestSlot = currentSlot;
        let best = { crossings: crossingBySlot[currentSlot], span: spanBySlot[currentSlot] };
        for (let slot = 0; slot <= others.length; slot += 1) {
          const score = { crossings: crossingBySlot[slot], span: spanBySlot[slot] };
          if (compareScore(score, best) < 0) {
            best = score;
            bestSlot = slot;
          }
        }
        if (bestSlot === currentSlot) continue;
        layer.splice(currentSlot, 1);
        layer.splice(bestSlot, 0, id);
        reindex(layerIndex);
        anyChange = true;
      }
      return anyChange;
    };

    const maxLayer = layers.length - 1;
    const downward = () => {
      for (let index = 1; index <= maxLayer; index += 1) {
        sortLayer(index, (vertex) => vertex.down);
        consider();
      }
    };
    const upward = () => {
      for (let index = maxLayer - 1; index >= 0; index -= 1) {
        sortLayer(index, (vertex) => vertex.up);
        consider();
      }
    };

    consider();
    for (let round = 0; round < ORDER_ROUNDS; round += 1) {
      const upwardFirst = (round % 2 === 0) === startUpward;
      if (upwardFirst) { upward(); downward(); }
      else { downward(); upward(); }
    }
    bestLayers.forEach((layer, index) => { layers[index] = [...layer]; });
    position.clear();
    layers.forEach((layer) => layer.forEach((id, slot) => position.set(id, slot)));
    for (let pass = 0; pass < SIFT_ROUNDS; pass += 1) {
      let improved = false;
      const upwardFirst = (pass % 2 === 0) === startUpward;
      const order = upwardFirst
        ? Array.from({ length: maxLayer + 1 }, (_, index) => maxLayer - index)
        : Array.from({ length: maxLayer + 1 }, (_, index) => index);
      for (const index of order) {
        improved = siftLayer(index, pass % 2 === 1) || improved;
        consider();
      }
      if (!improved) break;
    }
    return { layers: bestLayers, score: bestScore };
  }

  /** Return the rank bands in which two original edge chains cross. */
  function crossingBands(firstChain, secondChain, vertices, position) {
    const firstStart = vertices.get(firstChain[0]).layer;
    const secondStart = vertices.get(secondChain[0]).layer;
    const firstEnd = vertices.get(firstChain[firstChain.length - 1]).layer;
    const secondEnd = vertices.get(secondChain[secondChain.length - 1]).layer;
    const start = Math.max(firstStart, secondStart);
    const end = Math.min(firstEnd, secondEnd);
    const bands = [];
    for (let layer = start; layer < end; layer += 1) {
      const firstLower = firstChain[layer - firstStart];
      const firstUpper = firstChain[layer + 1 - firstStart];
      const secondLower = secondChain[layer - secondStart];
      const secondUpper = secondChain[layer + 1 - secondStart];
      if (firstLower === secondLower || firstUpper === secondUpper) continue;
      const lower = position.get(firstLower) - position.get(secondLower);
      const upper = position.get(firstUpper) - position.get(secondUpper);
      if (lower * upper < 0) bands.push(layer);
    }
    return bands;
  }

  /** If two edges form a lens (cross, separate, then cross again), exchange
   * their dummy slots inside the lens. The occupied slots in every rank stay
   * unchanged, so crossings with all other edges are preserved, while the two
   * crossings forming the lens disappear. Repeating this yields the useful
   * pseudoline invariant: every pair of original edges crosses at most once. */
  function removeRepeatedCrossings(layers, chains, vertices, segmentsByLayer) {
    const position = positionsOf(layers);
    // An edge that spans fewer than two rank bands cannot cross another edge
    // twice. Excluding it avoids a quadratic scan of ordinary adjacent-rank
    // edges, which are the majority in dense DAGs.
    const eligibleChains = chains.filter((chain) =>
      vertices.get(chain[chain.length - 1]).layer - vertices.get(chain[0]).layer >= 2);
    const limit = Math.max(1, eligibleChains.length * eligibleChains.length * layers.length);
    let changes = 0;
    let changed = true;
    while (changed && changes < limit) {
      changed = false;
      scan:
      for (let first = 0; first < eligibleChains.length; first += 1)
        for (let second = first + 1; second < eligibleChains.length; second += 1) {
          if (changes >= limit) break scan;
          const firstChain = eligibleChains[first];
          const secondChain = eligibleChains[second];
          const firstStart = vertices.get(firstChain[0]).layer;
          const secondStart = vertices.get(secondChain[0]).layer;
          const overlap = Math.min(
            vertices.get(firstChain[firstChain.length - 1]).layer,
            vertices.get(secondChain[secondChain.length - 1]).layer,
          ) - Math.max(firstStart, secondStart);
          if (overlap < 2) continue;
          const bands = crossingBands(firstChain, secondChain, vertices, position);
          if (bands.length < 2) continue;
          const fromLayer = bands[0] + 1;
          const throughLayer = bands[1];
          const swaps = [];
          for (let layer = fromLayer; layer <= throughLayer; layer += 1) {
            const firstId = firstChain[layer - firstStart];
            const secondId = secondChain[layer - secondStart];
            if (!vertices.get(firstId).virtual || !vertices.get(secondId).virtual) {
              swaps.length = 0;
              break;
            }
            swaps.push({
              layer,
              firstId,
              secondId,
              firstSlot: position.get(firstId),
              secondSlot: position.get(secondId),
            });
          }
          if (!swaps.length) continue;

          // Only the bands touching a swapped rank can change. Checking that
          // interval preserves the safety guard without rescoring the graph.
          const crossingScore = () => {
            let total = 0;
            for (let layer = fromLayer - 1; layer <= throughLayer; layer += 1)
              total += countCrossingsBetween(segmentsByLayer[layer] || [], position);
            return total;
          };
          const before = crossingScore();
          for (const swap of swaps) {
            layers[swap.layer][swap.firstSlot] = swap.secondId;
            layers[swap.layer][swap.secondSlot] = swap.firstId;
            position.set(swap.firstId, swap.secondSlot);
            position.set(swap.secondId, swap.firstSlot);
          }
          const after = crossingScore();
          if (after >= before) {
            for (const swap of swaps) {
              layers[swap.layer][swap.firstSlot] = swap.firstId;
              layers[swap.layer][swap.secondSlot] = swap.secondId;
              position.set(swap.firstId, swap.firstSlot);
              position.set(swap.secondId, swap.secondSlot);
            }
            continue;
          }
          changes += 1;
          changed = true;
        }
    }
    return position;
  }

  /** Weighted isotonic regression for an ordered rank with non-overlap
   * constraints. Transforming away the pairwise separations reduces it to
   * ordinary monotonic regression solved by pooled adjacent violators. */
  function packOrdered(items) {
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

  function gapBetween(first, second, nodeGap) {
    // Parallel edge corridors need visible air even after antialiasing and
    // rounded-corner trimming. With two 2px dummy vertices this yields 14px
    // between their centre lines.
    if (first.virtual && second.virtual) return 12;
    if (first.virtual || second.virtual) return Math.min(18, nodeGap);
    return nodeGap;
  }

  /** Constrained coordinate descent. Dummy vertices receive strong weight at
   * the mean of their two chain neighbours, which is the zero-curvature
   * position. Real vertices remain free to balance all incident edges. */
  function assignCoordinates(layers, vertices, nodeGap) {
    const x = new Map();
    const rankWidths = layers.map((layer) => layer.reduce((width, id, index) => {
      const vertex = vertices.get(id);
      if (index === 0) return vertex.width;
      const previous = vertices.get(layer[index - 1]);
      return width + gapBetween(previous, vertex, nodeGap) + vertex.width;
    }, 0));
    const widest = Math.max(...rankWidths);
    layers.forEach((layer, layerIndex) => {
      let cursor = (widest - rankWidths[layerIndex]) / 2;
      layer.forEach((id, index) => {
        const vertex = vertices.get(id);
        if (index > 0) {
          const previous = vertices.get(layer[index - 1]);
          cursor += gapBetween(previous, vertex, nodeGap);
        }
        x.set(id, cursor + vertex.width / 2);
        cursor += vertex.width;
      });
    });

    const relax = (layer, neighborsOf) => {
      const items = layer.map((id, index) => {
        const vertex = vertices.get(id);
        const neighbors = neighborsOf(vertex);
        const desired = neighbors.length
          ? neighbors.reduce((sum, neighbor) => sum + x.get(neighbor), 0) / neighbors.length
          : x.get(id);
        const next = layer[index + 1];
        const sep = next
          ? vertex.width / 2 + vertices.get(next).width / 2 +
            gapBetween(vertex, vertices.get(next), nodeGap)
          : 0;
        return {
          desired,
          weight: neighbors.length ? (vertex.virtual ? 32 : Math.sqrt(neighbors.length)) : 0.001,
          sep,
        };
      });
      packOrdered(items).forEach((value, index) => x.set(layer[index], value));
    };

    const maxLayer = layers.length - 1;
    for (let round = 0; round < POSITION_ROUNDS; round += 1) {
      for (let index = 1; index <= maxLayer; index += 1)
        relax(layers[index], (vertex) => vertex.down);
      for (let index = maxLayer - 1; index >= 0; index -= 1)
        relax(layers[index], (vertex) => vertex.up);
      for (let index = 0; index <= maxLayer; index += 1)
        relax(layers[index], (vertex) => [...vertex.down, ...vertex.up]);
    }
    return x;
  }

  /** Align every maximal feasible run of an edge's dummy vertices to one
   * vertical track. A run is split only when the free horizontal intervals in
   * its ranks have empty intersection; consequently every retained change of
   * track is forced by an intervening vertex or another edge lane. */
  function straightenDummyChains(chains, layers, vertices, x, nodeGap) {
    const slotOf = positionsOf(layers);
    const intervalOf = (id) => {
      const vertex = vertices.get(id);
      const layer = layers[vertex.layer];
      const slot = slotOf.get(id);
      let lower = -Infinity;
      let upper = Infinity;
      if (slot > 0) {
        const left = vertices.get(layer[slot - 1]);
        lower = x.get(left.id) + left.width / 2 + vertex.width / 2 +
          gapBetween(left, vertex, nodeGap);
      }
      if (slot + 1 < layer.length) {
        const right = vertices.get(layer[slot + 1]);
        upper = x.get(right.id) - right.width / 2 - vertex.width / 2 -
          gapBetween(vertex, right, nodeGap);
      }
      return { lower, upper };
    };
    const place = (chain, run, lower, upper) => {
      const desired = run.map((id) => x.get(id));
      if (run[0] === chain[1]) desired.push(x.get(chain[0]));
      if (run[run.length - 1] === chain[chain.length - 2])
        desired.push(x.get(chain[chain.length - 1]));
      const target = median(desired);
      const track = Math.max(lower, Math.min(upper, target));
      for (const id of run) x.set(id, track);
    };

    // Longer chains first: they benefit most and establish stable corridors
    // for the shorter chains packed beside them.
    [...chains]
      .sort((a, b) => b.length - a.length || compareText(a.join('\0'), b.join('\0')))
      .forEach((chain) => {
        const dummies = chain.slice(1, -1);
        if (dummies.length < 2) return;
        let run = [];
        let lower = -Infinity;
        let upper = Infinity;
        for (const id of dummies) {
          const interval = intervalOf(id);
          const nextLower = Math.max(lower, interval.lower);
          const nextUpper = Math.min(upper, interval.upper);
          if (run.length && nextLower > nextUpper) {
            place(chain, run, lower, upper);
            run = [];
            lower = interval.lower;
            upper = interval.upper;
          } else {
            lower = nextLower;
            upper = nextUpper;
          }
          run.push(id);
        }
        if (run.length) place(chain, run, lower, upper);
      });
  }

  /** Collapse selected edge chains into vertical alignment blocks, then pack
   * those blocks against every rank's non-overlap constraints. This is used
   * for proof-to-conclusion edges and sole assumptions: their statements,
   * proof boxes, and any dummy vertices share one x coordinate without
   * allowing boxes to collide. */
  function alignEdgeChains(edgeIndices, chains, layers, vertices, x, nodeGap) {
    if (!edgeIndices.length) return;
    const parent = new Map([...vertices.keys()].map((id) => [id, id]));
    const find = (id) => {
      let root = id;
      while (parent.get(root) !== root) root = parent.get(root);
      while (parent.get(id) !== id) {
        const next = parent.get(id);
        parent.set(id, root);
        id = next;
      }
      return root;
    };
    const union = (first, second) => {
      const a = find(first);
      const b = find(second);
      if (a === b) return;
      if (compareText(a, b) < 0) parent.set(b, a);
      else parent.set(a, b);
    };
    [...new Set(edgeIndices)].sort((a, b) => a - b).forEach((edgeIndex) => {
      const chain = chains[edgeIndex];
      if (!chain) return;
      for (let index = 1; index < chain.length; index += 1)
        union(chain[0], chain[index]);
    });

    const members = new Map();
    for (const id of vertices.keys()) {
      const root = find(id);
      if (!members.has(root)) members.set(root, []);
      members.get(root).push(id);
    }
    // Two vertices in one rank cannot occupy the same alignment track. This
    // only arises from contradictory requested alignments (for example, two
    // same-rank proofs forced to the same zero-width conclusion port).
    for (const ids of members.values()) {
      const occupied = new Set();
      for (const id of ids) {
        const layer = vertices.get(id).layer;
        if (occupied.has(layer)) return;
        occupied.add(layer);
      }
    }

    const constraints = new Map();
    const outgoing = new Map([...members.keys()].map((root) => [root, new Map()]));
    const incoming = new Map([...members.keys()].map((root) => [root, new Set()]));
    for (const layer of layers)
      for (let slot = 0; slot + 1 < layer.length; slot += 1) {
        const leftId = layer[slot];
        const rightId = layer[slot + 1];
        const left = find(leftId);
        const right = find(rightId);
        if (left === right) return;
        const first = vertices.get(leftId);
        const second = vertices.get(rightId);
        const separation = first.width / 2 + second.width / 2 +
          gapBetween(first, second, nodeGap);
        const key = `${left}\u0001${right}`;
        if (separation <= (constraints.get(key) || 0)) continue;
        constraints.set(key, separation);
        outgoing.get(left).set(right, separation);
        incoming.get(right).add(left);
      }

    const indegree = new Map([...members.keys()].map((root) => [root, incoming.get(root).size]));
    const ready = [...members.keys()].filter((root) => indegree.get(root) === 0).sort(compareText);
    const order = [];
    while (ready.length) {
      const root = ready.shift();
      order.push(root);
      for (const next of [...outgoing.get(root).keys()].sort(compareText)) {
        indegree.set(next, indegree.get(next) - 1);
        if (indegree.get(next) === 0) {
          ready.push(next);
          ready.sort(compareText);
        }
      }
    }
    // Reversed alignment-block order in two ranks makes the equality system
    // infeasible. Leave the already safe unconstrained coordinates intact.
    if (order.length !== members.size) return;

    const desired = new Map([...members].map(([root, ids]) => [
      root,
      median(ids.map((id) => x.get(id))),
    ]));
    const blockX = new Map(desired);
    for (const root of order)
      for (const [next, separation] of outgoing.get(root))
        blockX.set(next, Math.max(blockX.get(next), blockX.get(root) + separation));

    // Translate each weak constraint component back toward its original
    // coordinates. Translation preserves every separation inequality.
    const neighbors = new Map([...members.keys()].map((root) => [root, new Set()]));
    for (const [root, targets] of outgoing)
      for (const next of targets.keys()) {
        neighbors.get(root).add(next);
        neighbors.get(next).add(root);
      }
    const seen = new Set();
    for (const root of [...members.keys()].sort(compareText)) {
      if (seen.has(root)) continue;
      const component = [];
      const stack = [root];
      seen.add(root);
      while (stack.length) {
        const current = stack.pop();
        component.push(current);
        for (const next of neighbors.get(current))
          if (!seen.has(next)) { seen.add(next); stack.push(next); }
      }
      const shift = median(component.map((id) => desired.get(id) - blockX.get(id)));
      for (const id of component) blockX.set(id, blockX.get(id) + shift);
    }
    for (const [root, ids] of members)
      for (const id of ids) x.set(id, blockX.get(root));
  }

  /** Remove an intermediate dummy point when it lies on the straight chord
   * between its neighbours. Only geometric no-ops disappear, so the route's
   * crossings and obstacle avoidance are unchanged. */
  function compactBends(points) {
    const result = [];
    for (const point of points) {
      while (result.length >= 2) {
        const first = result[result.length - 2];
        const middle = result[result.length - 1];
        const fraction = (middle.layer - first.layer) / (point.layer - first.layer);
        const expectedX = first.x + (point.x - first.x) * fraction;
        if (Math.abs(middle.x - expectedX) > 0.35) break;
        result.pop();
      }
      result.push(point);
    }
    return result;
  }

  /**
   * Lay out a DAG. Nodes carry `{ id, width }`; edges carry `{ from, to }`.
   * The result contains real-node positions, sparse bend routes, dimensions,
   * and crossing diagnostics used by invariant tests.
   */
  function layoutDag({ nodes, edges, nodeGap = 28, alignEdgeIndices = [] }) {
    if (!nodes.length) return {
      positions: new Map(), routes: [], rankRoutes: [], maxLayer: 0, width: 0,
      crossings: 0, maxPairCrossings: 0,
    };
    const incoming = new Map(nodes.map((node) => [node.id, []]));
    const outgoing = new Map(nodes.map((node) => [node.id, []]));
    for (const edge of edges) {
      incoming.get(edge.to).push(edge.from);
      outgoing.get(edge.from).push(edge.to);
    }
    const layerOf = assignLayers(nodes, incoming, outgoing);

    const vertices = new Map();
    for (const node of nodes)
      vertices.set(node.id, {
        id: node.id, width: node.width, layer: layerOf.get(node.id),
        up: [], down: [], virtual: false,
      });
    const chains = [];
    const segments = [];
    edges.forEach((edge, edgeIndex) => {
      const chain = [edge.from];
      let previous = edge.from;
      for (let layer = layerOf.get(edge.from) + 1; layer < layerOf.get(edge.to); layer += 1) {
        const id = `\0${edgeIndex}@${layer}`;
        vertices.set(id, {
          id, width: VIRTUAL_WIDTH, layer, up: [], down: [], virtual: true,
        });
        chain.push(id);
        segments.push({ lower: previous, upper: id });
        previous = id;
      }
      chain.push(edge.to);
      chains.push(chain);
      segments.push({ lower: previous, upper: edge.to });
    });
    for (const segment of segments) {
      vertices.get(segment.lower).up.push(segment.upper);
      vertices.get(segment.upper).down.push(segment.lower);
    }

    const maxLayer = Math.max(...[...layerOf.values()]);
    const baseLayers = Array.from({ length: maxLayer + 1 }, () => []);
    for (const vertex of vertices.values()) baseLayers[vertex.layer].push(vertex.id);
    baseLayers.forEach((layer) => layer.sort());
    const segmentsByLayer = Array.from({ length: maxLayer }, () => []);
    for (const segment of segments)
      segmentsByLayer[vertices.get(segment.lower).layer].push(segment);

    // Deterministic starts and two standard neighborhood centers find
    // different local minima on asymmetric graphs. Crossing count is primary;
    // total rank-span breaks ties.
    const alternatingSeed = baseLayers.map((layer, index) =>
      index % 2 ? [...layer].reverse() : [...layer]);
    const shuffledSeedA = shuffledLayers(baseLayers, 0x9e3779b9);
    const candidates = [
      optimizeOrdering(baseLayers, vertices, segments, segmentsByLayer, true, median),
      optimizeOrdering(baseLayers, vertices, segments, segmentsByLayer, false, barycenter),
    ];
    // Extra restarts pay off on the small archive figures. Proper layering can
    // add many dummy vertices, so larger workloads use the two strongest starts
    // and finalize only their best raw ordering to stay within an interaction
    // frame for ordinary graphs below 100 real vertices.
    const thoroughSearch = nodes.length <= FULL_SEARCH_NODE_LIMIT &&
      vertices.size <= FULL_SEARCH_VERTEX_LIMIT && segments.length <= FULL_SEARCH_SEGMENT_LIMIT;
    if (thoroughSearch) {
      candidates.push(
        optimizeOrdering(alternatingSeed, vertices, segments, segmentsByLayer, false, barycenter),
        optimizeOrdering(shuffledSeedA, vertices, segments, segmentsByLayer, true, barycenter),
      );
    }
    // Lens removal can improve small candidates by different amounts, so the
    // thorough path finalizes each one before choosing the overall minimum.
    const finalists = thoroughSearch
      ? candidates
      : [...candidates].sort((a, b) => compareScore(a.score, b.score) ||
        compareText(JSON.stringify(a.layers), JSON.stringify(b.layers))).slice(0, 1);
    const finalized = finalists.map((candidate) => {
      const layers = cloneLayers(candidate.layers);
      const position = removeRepeatedCrossings(layers, chains, vertices, segmentsByLayer);
      return {
        layers,
        position,
        score: {
          crossings: crossingCount(segmentsByLayer, position),
          span: spanScore(segments, position),
        },
      };
    });
    finalized.sort((a, b) => compareScore(a.score, b.score) ||
      compareText(JSON.stringify(a.layers), JSON.stringify(b.layers)));
    const { layers, position } = finalized[0];
    const crossings = finalized[0].score.crossings;
    let maxPairCrossings = crossings > 0 ? 1 : 0;
    const multiBandChains = chains.filter((chain) =>
      vertices.get(chain[chain.length - 1]).layer - vertices.get(chain[0]).layer >= 2);
    for (let first = 0; first < multiBandChains.length; first += 1)
      for (let second = first + 1; second < multiBandChains.length; second += 1)
        maxPairCrossings = Math.max(maxPairCrossings,
          crossingBands(multiBandChains[first], multiBandChains[second], vertices, position).length);

    const x = assignCoordinates(layers, vertices, nodeGap);
    straightenDummyChains(chains, layers, vertices, x, nodeGap);
    alignEdgeChains(alignEdgeIndices, chains, layers, vertices, x, nodeGap);
    let minEdge = Infinity;
    let maxEdge = -Infinity;
    for (const vertex of vertices.values()) {
      minEdge = Math.min(minEdge, x.get(vertex.id) - vertex.width / 2);
      maxEdge = Math.max(maxEdge, x.get(vertex.id) + vertex.width / 2);
    }
    const pointOf = (id) => ({
      x: x.get(id) - minEdge,
      layer: vertices.get(id).layer,
    });
    const positions = new Map(nodes.map((node) => [node.id, pointOf(node.id)]));
    // Keep the complete proper-layer chain for obstacle-safe rendering. The
    // renderer uses these points to cross every intervening node row through
    // a reserved vertical corridor, while `routes` remains the minimal list
    // of geometrically meaningful bends for diagnostics and other consumers.
    const rankRoutes = chains.map((chain) => chain.slice(1, -1).map(pointOf));
    const routes = chains.map((chain) =>
      compactBends(chain.map(pointOf)).slice(1, -1));

    return {
      positions,
      routes,
      rankRoutes,
      maxLayer,
      width: maxEdge - minEdge,
      crossings,
      maxPairCrossings,
    };
  }

  globalThis.laxLayout = { layoutDag };
})();
