// Development evidence only. Geometry predicates come from the independent
// validator, never the ordering or routing optimizer. Run npm run build first.
import { commandBends, CURVE_DEVIATION, flattenCommands, parsePathData, routeMetrics, segmentHitsRect } from '../dist/graph-layout/validate.js';
import { indexedGraph, stronglyConnectedComponents, weakComponents } from '../dist/graph-layout/components.js';

export const METRICS_VERSION = 'final-geometry-v1';
const pointKey = (p) => `${Math.round(p.x * 1e5)},${Math.round(p.y * 1e5)}`;
const overlaps = (a, b) => Math.min(a.x + a.width, b.x + b.width) > Math.max(a.x, b.x) + 1e-5 && Math.min(a.y + a.height, b.y + b.height) > Math.max(a.y, b.y) + 1e-5;
const contains = (a, b, tolerance = .003) => a.x <= b.x + tolerance && a.y <= b.y + tolerance && a.x + a.width >= b.x + b.width - tolerance && a.y + a.height >= b.y + b.height - tolerance;
const union = (a, b) => ({ x: Math.min(a.x, b.x), y: Math.min(a.y, b.y), width: Math.max(a.x + a.width, b.x + b.width) - Math.min(a.x, b.x), height: Math.max(a.y + a.height, b.y + b.height) - Math.min(a.y, b.y) });
const at = (r, p) => ({ ...r, x: r.x + p.x, y: r.y + p.y });
const grow = (r, n) => ({ x: r.x - n, y: r.y - n, width: r.width + 2 * n, height: r.height + 2 * n });

export function distribution(values) {
  if (!values.length) return { count: 0, minimum: null, p50: null, p95: null, maximum: null, total: 0 };
  const sorted = [...values].sort((a, b) => a - b);
  return { count: sorted.length, minimum: sorted[0], p50: sorted[Math.ceil(sorted.length * .5) - 1], p95: sorted[Math.ceil(sorted.length * .95) - 1], maximum: sorted.at(-1), total: sorted.reduce((a, b) => a + b, 0) };
}
const histogram = (values) => Object.fromEntries([...new Set(values)].sort((a, b) => a - b).map((value) => [value, values.filter((v) => v === value).length]));

export function graphStatistics(fixture, measured, geometry, searchStats) {
  const graph = measured.graph, indexed = indexedGraph(graph), components = weakComponents(indexed.nodeCount, indexed.edges);
  const sccs = stronglyConnectedComponents(indexed.nodeCount, indexed.edges), sccOf = new Map(sccs.flatMap((s, i) => s.map((n) => [n, i])));
  const inDegree = Array(graph.nodes.length).fill(0), outDegree = [...inDegree];
  for (const edge of indexed.edges) { inDegree[edge.target]++; outDegree[edge.source]++; }
  const semantic = fixture.kind === 'proofs' ? { nodes: fixture.data.statements.length + fixture.data.proofs.length,
    edges: fixture.data.proofs.reduce((n, p) => n + p.assumptions.length + 1, 0), statements: fixture.data.statements.length, proofs: fixture.data.proofs.length }
    : { nodes: fixture.data.nodes.length, edges: fixture.data.edges.length, statements: 0, proofs: 0 };
  const result = { semantic, display: { nodes: graph.nodes.length, edges: graph.edges.length,
    incidencePorts: graph.nodes.reduce((n, v) => n + v.ports.length, 0), docks: measured.display.nodes.reduce((n, v) => n + v.docks.length, 0),
    weakComponents: components.length, sccSizes: sccs.map((s) => s.length).sort((a, b) => b - a),
    cyclicSccSizes: sccs.filter((s) => s.length > 1 || indexed.edges.some((e) => e.source === s[0] && e.target === s[0])).map((s) => s.length).sort((a, b) => b - a),
    inDegree: histogram(inDegree), outDegree: histogram(outDegree) },
    labels: { fontSize: 12, maxWrapWidth: 240, widths: distribution(graph.nodes.flatMap((n) => n.labelBoxes.map((b) => b.width))),
      heights: distribution(graph.nodes.flatMap((n) => n.labelBoxes.map((b) => b.height))),
      dimensions: graph.nodes.map((n) => ({ id: n.id, width: n.width, height: n.height, labelBoxes: n.labelBoxes })) } };
  if (!geometry) return result;
  const placed = new Map(geometry.nodes.map((n) => [n.id, n]));
  let D = 0, totalEdgeSpan = 0, internalFeedbackEdges = 0, rankUnavailableEdges = 0;
  for (const edge of indexed.edges) {
    if (sccOf.get(edge.source) === sccOf.get(edge.target)) { internalFeedbackEdges++; continue; }
    const source = placed.get(graph.nodes[edge.source].id)?.rank, target = placed.get(graph.nodes[edge.target].id)?.rank;
    if (source === undefined || target === undefined) { rankUnavailableEdges++; continue; }
    const span = target - source; totalEdgeSpan += span;
    if (edge.minRankSpan === 1) D += span - 1;
  }
  const ranks = components.map((members) => {
    const values = members.map((i) => placed.get(graph.nodes[i].id)?.rank).filter((r) => r !== undefined);
    return { count: values.length ? Math.max(...values) + 1 : 0, realWidths: histogram(values) };
  });
  result.ranking = { D, definition: 'sum(span - 1) for unit-minimum-span edges in the displayed condensation DAG; internal SCC incidences excluded',
    totalEdgeSpan, internalFeedbackEdges, rankUnavailableEdges, components: ranks,
    maximumRank: Math.max(-1, ...geometry.nodes.map((n) => n.rank ?? -1)),
    maximumRealRankWidth: Math.max(0, ...ranks.flatMap((r) => Object.values(r.realWidths))),
    searchMaximumExpandedRankWidth: searchStats?.maximumRankWidth ?? null,
    searchMaximumDummyExpansion: searchStats?.dummyVertices ?? null };
  return result;
}

/** Reconstruct only the frozen renderer's entity/array mapping. No old layout
 * calculations are reproduced. Every route and rectangle is captured output. */
export function legacyTopology(fixture) {
  const data = fixture.data;
  if (fixture.kind !== 'proofs') return {
    objects: data.nodes.map((n) => ({ id: n.id, owner: n.id, kind: 'node' })),
    links: data.edges.map((e, i) => ({ id: `legacy:${i}`, source: e.from, target: e.to, sourceEndpoint: e.from, targetEndpoint: e.to, kind: e.kind ?? 'import', multiplicity: 1 })),
    semanticEdges: data.edges.length,
  };
  const nodes = [], concepts = new Map(), place = new Map();
  for (const s of data.statements) {
    if ((s.count ?? 1) > 1 && s.concept) {
      let node = concepts.get(s.concept);
      if (!node) { node = { id: `c:${s.concept}`, owner: `c:${s.concept}`, kind: 'node', docks: [] }; concepts.set(s.concept, node); nodes.push(node); }
      node.docks[s.index - 1] = s;
      place.set(s.id, { nodeId: node.id, endpoint: s.id });
    } else { const id = `s:${s.id}`; nodes.push({ id, owner: id, kind: 'node' }); place.set(s.id, { nodeId: id, endpoint: s.id }); }
  }
  const objects = nodes.flatMap((n) => [n, ...(n.docks ?? []).filter(Boolean).map((s) => ({ id: `dock:${s.id}`, owner: n.id, kind: 'dock', semanticId: s.id }))]);
  for (const p of data.proofs) objects.push({ id: `p:${p.id}`, owner: `p:${p.id}`, kind: 'proof' });
  const links = [];
  for (const p of data.proofs) {
    const sources = new Map();
    for (const assumption of p.assumptions) {
      const endpoint = place.get(assumption); if (!endpoint) continue;
      const entry = sources.get(endpoint.nodeId) ?? []; entry.push(assumption); sources.set(endpoint.nodeId, entry);
    }
    for (const [source, assumptions] of sources) links.push({ id: `${p.id}:assumption:${source}`, source, target: `p:${p.id}`,
      sourceEndpoint: source, targetEndpoint: p.id, kind: 'assumption', multiplicity: assumptions.length });
    const end = place.get(p.conclusion);
    if (end) links.push({ id: `${p.id}:conclusion`, source: `p:${p.id}`, target: end.nodeId,
      sourceEndpoint: p.id, targetEndpoint: end.endpoint, kind: 'conclusion', multiplicity: 1 });
  }
  // This intentionally replays one frozen implementation's locale-dependent
  // sort; it is not used to canonicalize the new engine or the frozen split.
  const oldCollator = new Intl.Collator('en-US');
  links.sort((a, b) => oldCollator.compare(`${a.source}\0${a.target}`, `${b.source}\0${b.target}`));
  return { objects, links, semanticEdges: data.proofs.reduce((n, p) => n + p.assumptions.length + 1, 0) };
}

/** Quality of the actual old paths, including curves after shortcutting. */
export function oldOutputMetrics(fixture, capture) {
  const topology = legacyTopology(fixture), diagnostics = (capture.errors ?? []).map((message) => ({ code: 'old-browser-error', message }));
  if (capture.nodes.length !== topology.objects.length) diagnostics.push({ code: 'old-node-count', message: `Captured ${capture.nodes.length}; expected ${topology.objects.length} visible objects` });
  if (capture.paths.length !== topology.links.length) diagnostics.push({ code: 'old-route-count', message: `Captured ${capture.paths.length}; expected ${topology.links.length} legacy routes` });
  const owners = new Map(), obstacles = [];
  capture.nodes.forEach((node, i) => {
    const object = topology.objects[i]; if (!object) return;
    owners.set(object.owner, owners.has(object.owner) ? union(owners.get(object.owner), node.box) : node.box);
    obstacles.push({ ...object, box: node.box, ink: node.ink, label: node.label });
  });
  const nearOwner = (p, owner) => { const r = owners.get(owner); return r && contains(grow(r, .01), { ...p, width: 0, height: 0 }); };
  let bends = 0;
  const routes = capture.paths.map((path, i) => {
    const link = topology.links[i] ?? { id: `unmapped:${i}`, source: '', target: '', sourceEndpoint: `unmapped:${i}:s`, targetEndpoint: `unmapped:${i}:t` };
    const commands = parsePathData(path.d), points = flattenCommands(commands); bends += commandBends(commands);
    if (!points.length || !nearOwner(points[0], link.source) || !nearOwner(points.at(-1), link.target)) diagnostics.push({ code: 'old-attachment-unverified', message: 'Captured route terminals do not verify the frozen array mapping', ids: [link.id] });
    if (fixture.kind === 'proofs' && !path.kind.split(/\s+/).includes(link.kind)) diagnostics.push({ code: 'old-edge-kind', message: 'Captured edge class disagrees with the recovered incidence', ids: [link.id] });
    return { ...link, points, sourcePort: `${link.sourceEndpoint}:${pointKey(points[0] ?? { x: 0, y: 0 })}`, targetPort: `${link.targetEndpoint}:${pointKey(points.at(-1) ?? { x: 0, y: 0 })}` };
  });
  const collisions = [];
  for (const route of routes) for (const obstacle of obstacles) {
    if (route.source === obstacle.owner || route.target === obstacle.owner) continue;
    for (const [kind, box] of [['body-or-dock', obstacle.box], ['label', obstacle.ink]]) {
      if (!box || !route.points.slice(1).some((b, i) => segmentHitsRect(route.points[i], b, grow(box, CURVE_DEVIATION)))) continue;
      collisions.push({ edgeId: route.id, objectId: obstacle.id, kind });
    }
  }
  const nodeOverlaps = [];
  for (let i = 0; i < obstacles.length; i++) for (let j = i + 1; j < obstacles.length; j++) if (obstacles[i].owner !== obstacles[j].owner && overlaps(obstacles[i].box, obstacles[j].box)) nodeOverlaps.push([obstacles[i].id, obstacles[j].id]);
  const shortenedLabels = obstacles.filter((o) => o.kind !== 'proof' && o.label?.includes('…')).map((o) => o.id);
  const clippedLabels = obstacles.filter((o) => o.ink && !contains(o.box, o.ink)).map((o) => o.id);
  const coalesced = topology.links.filter((e) => e.multiplicity > 1).map((e) => ({ id: e.id, multiplicity: e.multiplicity }));
  const metrics = { ...routeMetrics(routes, { x: 0, y: 0, width: capture.width, height: capture.height }), bends };
  return { metrics, diagnostics, visibleObjects: capture.nodes.length, renderedEdges: capture.paths.length, semanticEdges: topology.semanticEdges,
    comparableIncidences: !diagnostics.length && !coalesced.length && capture.paths.length === topology.semanticEdges,
    coalescedIncidences: coalesced, collisions, nodeOverlaps, shortenedLabels, clippedLabels,
    limitations: ['Old output uses its actual truncated labels/identifiers; both renderers use 12px body labels, while measured box sizes can differ. Old numbered docks used 7.5px monospace; new docks use measured 12px regular text.',
      'The old capture does not encode port contracts or arrowhead geometry; full new-contract validation is not claimed.',
      'Frozen proof-link order is replayed using the old en-US locale comparison and checked against captured terminals.'] };
}

export function metricComparison(before, after) {
  if (!before || !before.comparableIncidences) return { comparable: false, reason: before ? 'Old incidence multiplicity or terminal mapping differs or is unverifiable' : 'No old capture', deltas: null, regressions: [] };
  const keys = ['crossings', 'repeatedCrossingPairs', 'endpointTouches', 'tangencies', 'multiwayCrossings', 'overlaps', 'bends', 'length', 'width', 'height'];
  const deltas = Object.fromEntries(keys.map((key) => [key, after[key] - before.metrics[key]]));
  const priorAngle = before.metrics.minimumCrossingAngle, nextAngle = after.minimumCrossingAngle;
  deltas.minimumCrossingAngle = Number.isFinite(priorAngle) && Number.isFinite(nextAngle) ? nextAngle - priorAngle : null;
  const regressions = keys.filter((key) => deltas[key] > 1e-5);
  if (deltas.minimumCrossingAngle !== null && deltas.minimumCrossingAngle < -1e-5) regressions.push('minimumCrossingAngle');
  return { comparable: true, equalNodeSizes: false, deltas, regressions,
    crossingAngleComparison: deltas.minimumCrossingAngle !== null ? 'both diagrams have proper crossings'
      : Number.isFinite(nextAngle) ? 'proper crossings appear; no earlier angle exists'
        : Number.isFinite(priorAngle) ? 'proper crossings disappear; no later angle exists' : 'neither diagram has a proper crossing angle',
    interpretation: 'Every cost increase and defined crossing-angle decrease is listed; extra extent or bends may accompany larger readable labels and safe terminal adapters. No scalar average hides regressions.' };
}

export function visibleContentBounds(graph, geometry) {
  const points = geometry.edges.flatMap((e) => e.sections.flatMap((s) => s.commands ? flattenCommands(s.commands) : s.points));
  const rectangles = geometry.nodes.flatMap((n) => {
    const spec = graph.nodes.find((s) => s.id === n.id);
    return [n, ...(spec?.labelBoxes ?? []).map((b) => at(b, n))];
  });
  if (!points.length && !rectangles.length) return { x: 0, y: 0, width: 0, height: 0 };
  const xs = [...points.map((p) => p.x), ...rectangles.flatMap((r) => [r.x, r.x + r.width])], ys = [...points.map((p) => p.y), ...rectangles.flatMap((r) => [r.y, r.y + r.height])];
  return { x: Math.min(...xs), y: Math.min(...ys), width: Math.max(...xs) - Math.min(...xs), height: Math.max(...ys) - Math.min(...ys) };
}
