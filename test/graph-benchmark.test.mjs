import { describe, expect, test } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { distribution, legacyTopology, metricComparison, oldOutputMetrics } from '../scripts/graph-metrics.mjs';
import { checkedFinalGeometry, layoutInputDigest, summarizeRows } from '../scripts/graph-benchmark.mjs';
import { fromDot, fromElk, toDot, toElk, unsupportedReasons } from '../scripts/graph-baselines.mjs';
import { layoutGraph } from '../dist/graph-layout/index.js';
import { copyGraphReportAssets, graphReportPage } from '../scripts/graph-report-assets.mjs';

const measuredPair = (fixed = false) => ({ nodes: [
  { id: 'a', kind: 'concept', width: 40, height: 30, labelBoxes: [], ports: [{ id: 's', nodeId: 'a', semanticEndpointId: 'A', side: 'north', mode: fixed ? 'fixed-position' : 'free-on-side', ...(fixed ? { offset: { x: 12, y: 0 } } : {}) }] },
  { id: 'b', kind: 'concept', width: 50, height: 30, labelBoxes: [], ports: [{ id: 't', nodeId: 'b', semanticEndpointId: 'B', side: 'south', mode: fixed ? 'fixed-position' : 'free-on-side', ...(fixed ? { offset: { x: 30, y: 30 } } : {}) }] },
], edges: [{ id: 'edge', sourcePortId: 's', targetPortId: 't', kind: 'import', minRankSpan: 1, semanticIds: ['original-edge'] }] });

describe('frozen benchmark metric boundaries', () => {
  test('numbered dock measurements participate in the layout input digest', () => {
    const measured = { graph: { nodes: [], edges: [] }, display: { kind: 'proofs', nodes: [
      { id: 'concept', kind: 'concept', label: 'Concept', docks: [{ ordinal: 2 }] },
    ] } };
    const labels = new Map([['Concept', { signature: 'title' }], ['2', { signature: 'dock-v1' }]]);
    const first = layoutInputDigest(measured, labels, { signature: 'font' });
    labels.set('2', { signature: 'dock-v2' });
    expect(layoutInputDigest(measured, labels, { signature: 'font' })).not.toBe(first);
  });
  test('evidence pages carry portable exact fonts and retain native SVG dimensions', () => {
    const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'lax-report-assets-'));
    try {
      const manifest = copyGraphReportAssets(directory);
      expect(manifest.filter((a) => a.file.endsWith('.woff2'))).toHaveLength(6);
      for (const entry of manifest) expect(createHash('sha256').update(fs.readFileSync(path.join(directory, entry.file))).digest('hex')).toBe(entry.sha256);
      const html = graphReportPage('<svg width="2400" height="1400"></svg>', 'A graph');
      expect(html).toContain('href="../assets/style.css"'); expect(html).toContain('width="2400" height="1400"');
      expect(html).not.toContain('/home/');
    } finally { fs.rmSync(directory, { recursive: true, force: true }); }
  });
  test('nearest-rank percentiles include all failures separately from valid geometry', () => {
    expect(distribution([])).toMatchObject({ count: 0, p50: null, p95: null });
    expect(distribution([4, 2, 1, 3])).toEqual({ count: 4, minimum: 1, p50: 2, p95: 4, maximum: 4, total: 10 });
    const rows = [{ id: 'ok', cohort: 'archive', split: 'held-out', kind: 'concepts', status: 'valid',
      after: { metrics: { crossings: 0, width: 10, height: 20 } }, comparison: { comparable: true, deltas: { crossings: -1 }, regressions: ['height'] } },
    { id: 'failure', cohort: 'archive', split: 'held-out', kind: 'concepts', status: 'failed', diagnostics: [{ code: 'bad', message: 'bad' }] }];
    const summary = summarizeRows(rows)['archive:held-out'];
    expect(summary).toMatchObject({ graphs: 2, valid: 1, failed: 1, comparableOldOutputs: 1, anyMetricRegression: 1 });
    expect(summary.failures[0].id).toBe('failure');
  });

  test('metrics measure the actual old post-shortcut routes', () => {
    const fixture = { kind: 'concepts', data: { nodes: ['a', 'b', 'c', 'd'].map((id) => ({ id })), edges: [{ from: 'a', to: 'd' }, { from: 'b', to: 'c' }] } };
    const capture = { width: 100, height: 100, errors: [], nodes: [
      { box: { x: 0, y: 90, width: 10, height: 10 } }, { box: { x: 90, y: 90, width: 10, height: 10 } },
      { box: { x: 0, y: 0, width: 10, height: 10 } }, { box: { x: 90, y: 0, width: 10, height: 10 } },
    ], paths: [{ d: 'M5,90 L95,10', kind: 'dag-edge' }, { d: 'M95,90 L5,10', kind: 'dag-edge' }] };
    const metrics = oldOutputMetrics(fixture, capture);
    expect(metrics.comparableIncidences).toBe(true);
    expect(metrics.metrics).toMatchObject({ crossings: 1, bends: 0, overlaps: 0 });
    capture.paths.pop();
    expect(oldOutputMetrics(fixture, capture).comparableIncidences).toBe(false);
  });

  test('coalesced proof assumptions cannot earn an equal-semantics verdict', () => {
    const fixture = { kind: 'proofs', data: { statements: [
      { id: 'a.1', concept: 'a', count: 2, index: 1 }, { id: 'a.2', concept: 'a', count: 2, index: 2 }, { id: 'b' },
    ], proofs: [{ id: 'p', assumptions: ['a.1', 'a.2'], conclusion: 'b' }] } };
    const topology = legacyTopology(fixture);
    expect(topology.semanticEdges).toBe(3); expect(topology.links).toHaveLength(2);
    expect(topology.links.find((l) => l.kind === 'assumption').multiplicity).toBe(2);
    expect(metricComparison({ comparableIncidences: false }, { crossings: 0 }).deltas).toBeNull();
  });

  test('every increased metric survives even when crossings improve', () => {
    const before = { comparableIncidences: true, metrics: { crossings: 2, repeatedCrossingPairs: 0, endpointTouches: 0, tangencies: 0, multiwayCrossings: 0, overlaps: 0, bends: 1, length: 50, width: 100, height: 40 } };
    const comparison = metricComparison(before, { ...before.metrics, crossings: 1, bends: 4, width: 101 });
    expect(comparison.deltas.crossings).toBe(-1);
    expect(comparison.regressions).toEqual(['bends', 'width']);
  });

  test('smaller crossing angles are regressions only when both angles exist', () => {
    const metrics = { crossings: 1, repeatedCrossingPairs: 0, endpointTouches: 0, tangencies: 0, multiwayCrossings: 0,
      overlaps: 0, bends: 2, length: 50, width: 100, height: 40, minimumCrossingAngle: 60 };
    const before = { comparableIncidences: true, metrics };
    const smaller = metricComparison(before, { ...metrics, minimumCrossingAngle: 30 });
    expect(smaller.deltas.minimumCrossingAngle).toBe(-30);
    expect(smaller.regressions).toEqual(['minimumCrossingAngle']);
    const disappears = metricComparison(before, { ...metrics, crossings: 0, minimumCrossingAngle: null });
    expect(disappears.deltas.minimumCrossingAngle).toBeNull(); expect(disappears.regressions).toEqual([]);
    const appears = metricComparison({ ...before, metrics: { ...metrics, crossings: 0, minimumCrossingAngle: null } }, metrics);
    expect(appears.deltas.minimumCrossingAngle).toBeNull(); expect(appears.regressions).toEqual(['crossings']);
  });

  test('serialized quantized output is independently checked', () => {
    const graph = measuredPair(), result = layoutGraph(graph, { inputDigest: 'test' });
    expect(checkedFinalGeometry(graph, result.geometry).metrics.crossings).toBe(0);
    const broken = structuredClone(result.geometry); broken.edges[0].sections.at(-1).terminalTargetPortId = 'wrong-port';
    expect(() => checkedFinalGeometry(graph, broken)).toThrow('Independent serialized geometry validation failed');
  });
});

describe('isolated comparator adapters', () => {
  test('dot retains each incidence and fixed measurements without hidden concentration', () => {
    const graph = measuredPair(); graph.nodes[0].width = 40.123;
    graph.edges.push({ ...graph.edges[0], id: 'parallel', semanticIds: ['second-original'] });
    const dot = toDot(graph);
    expect(dot.match(/n0 -> n1/g)).toHaveLength(2);
    expect(dot).toContain('concentrate=false'); expect(dot).toContain('id="parallel"');
    expect(dot).toContain((40.123 * 1000 / 72).toPrecision(16));
    expect(unsupportedReasons(measuredPair(true), 'graphviz')).not.toHaveLength(0);
  });

  test('flat Graphviz conversion reads the actual high precision polygons', () => {
    const graph = measuredPair(), output = { bb: '0,0,50000,100000', _draw_: [{ op: 'P', points: [[0, 0], [50000, 0], [50000, 100000], [0, 100000]] }],
      objects: [{ _gvid: 0, name: 'n0', _draw_: [{ op: 'p', points: [[5000, 0], [45000, 0], [45000, 30000], [5000, 30000]] }] },
        { _gvid: 1, name: 'n1', _draw_: [{ op: 'p', points: [[0, 70000], [50000, 70000], [50000, 100000], [0, 100000]] }] }],
      edges: [{ id: 'edge', tail: 0, head: 1, _draw_: [{ op: 'b', points: [[25000, 30000], [25000, 40000], [25000, 50000], [25000, 63000]] }],
        _hdraw_: [{ op: 'P', points: [[22000, 63000], [25000, 70000], [28000, 63000]] }] }] };
    const geometry = fromDot(graph, output, 'test');
    expect(geometry.nodes.map((n) => n.width)).toEqual([40, 50]);
    expect(geometry.edges[0].sections[0].points.at(-1)).toEqual({ x: 25, y: 30 });
    expect(checkedFinalGeometry(graph, geometry).metrics.crossings).toBe(0);
  });

  test('ELK receives hard fixed dock positions and preserves identities on return', () => {
    const graph = measuredPair(true), request = toElk(graph);
    expect(request.children[0].layoutOptions['elk.portConstraints']).toBe('FIXED_POS');
    expect(request.children[0].ports[0]).toMatchObject({ id: 's', x: 12, y: 0 });
    expect(request.edges).toEqual([{ id: 'edge', sources: ['s'], targets: ['t'] }]);
    const output = { width: 100, height: 100,
      children: [{ ...request.children[0], x: 18, y: 70 }, { ...request.children[1], x: 0, y: 0 }],
      edges: [{ ...request.edges[0], sections: [{ id: 'e0', startPoint: { x: 30, y: 70 }, endPoint: { x: 30, y: 30 } }] }] };
    const geometry = fromElk(graph, output, 'test');
    expect(geometry.edges[0].sections[0].terminalTargetPortId).toBe('t');
    expect(checkedFinalGeometry(graph, geometry).metrics.length).toBe(40);
    output.edges[0].sources = ['other']; expect(() => fromElk(graph, output, 'test')).toThrow('changed incidence');
  });

  test('SCC and mixed-port cases are reported unsupported without deleting edges', () => {
    const graph = measuredPair(); graph.edges.push({ ...graph.edges[0], id: 'back', sourcePortId: 't', targetPortId: 's' });
    expect(unsupportedReasons(graph, 'graphviz')[0]).toContain('expanded SCC');
    expect(unsupportedReasons(graph, 'elkjs')[0]).toContain('expanded SCC');
    expect(graph.edges).toHaveLength(2);
  });
});
