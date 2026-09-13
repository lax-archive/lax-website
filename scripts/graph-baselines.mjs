// OPTIONAL DEVELOPMENT COMPARATORS. Never imported by site builds or assets.
// Both engines receive the same measured nodes and uncoalesced semantic edges.
// No install/download occurs here. Unsupported constraints are explicit rows.
import fs from 'node:fs';
import path from 'node:path';
import { performance } from 'node:perf_hooks';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { canonical, digest } from './graph-inventory.mjs';
import { METRICS_VERSION, distribution } from './graph-metrics.mjs';
import { copyGraphReportAssets, graphReportPage } from './graph-report-assets.mjs';
import { indexedGraph, stronglyConnectedComponents } from '../dist/graph-layout/components.js';
import { quantizeGeometry } from '../dist/graph-layout/geometry.js';
import { validateGeometry } from '../dist/graph-layout/validate.js';
import { graphSvg } from '../dist/sitegen/graph-svg.js';

export const COMPARATOR_PINS = Object.freeze({ graphviz: '2.43.0', elkjs: '0.12.0' });
const SCALE = 1000; // integer Graphviz points per px; preserves 0.001px sizes
const quote = (text) => JSON.stringify(text);
const write = (file, value) => { fs.mkdirSync(path.dirname(file), { recursive: true }); fs.writeFileSync(file, canonical(value) + '\n'); };
const diagnosticsOf = (error) => error?.diagnostics ?? [{ code: error?.code ?? 'comparator-error', message: String(error.message ?? error) }];

export function unsupportedReasons(graph, engine) {
  const reasons = [], indexed = indexedGraph(graph), sccs = stronglyConnectedComponents(indexed.nodeCount, indexed.edges);
  if (sccs.some((s) => s.length > 1) || indexed.edges.some((e) => e.source === e.target)) reasons.push('expanded SCC groups require a compound comparator adapter; no flat replacement is made');
  if (graph.edges.some((e) => e.minRankSpan !== 1) && engine === 'elkjs') reasons.push('ELK comparator does not map nonunit rank-span constraints');
  if (engine === 'graphviz' && graph.nodes.some((n) => n.ports.some((p) => p.mode !== 'free-on-side'))) reasons.push('fixed numbered/order/position ports are outside the flat dot adapter');
  if (engine === 'graphviz' && graph.nodes.some((n) => n.footprints?.some((f) => f.kind === 'dock'))) reasons.push('numbered dock glyphs require an explicit dot compound/port adapter');
  if (engine === 'elkjs' && graph.nodes.some((n) => new Set(n.ports.map((p) => p.mode)).size > 1)) reasons.push('mixed free/fixed port constraints on one box are not silently strengthened');
  if (engine === 'elkjs' && graph.nodes.some((n) => n.ports.some((p) => p.mode === 'fixed-order') &&
    ['north', 'south', 'east', 'west'].some((side) => { const ps = n.ports.filter((p) => p.side === side); return new Set(ps.map((p) => p.order)).size !== ps.length; }))) reasons.push('equal ordered port blocks require a dedicated ELK group adapter');
  return reasons;
}

export function toDot(graph) {
  const ids = new Map(graph.nodes.map((n, i) => [n.id, `n${i}`])), ports = new Map(graph.nodes.flatMap((n) => n.ports.map((p) => [p.id, p])));
  const inch = (px) => (px * SCALE / 72).toPrecision(16);
  return ['digraph Lax {', `graph [rankdir=BT, splines=polyline, nodesep=${inch(28)}, ranksep=${inch(32)}, margin=0, pad=0, concentrate=false];`,
    'node [shape=box, fixedsize=true, label="", margin=0];',
    `edge [arrowhead=normal, arrowsize=${.7 * SCALE}];`,
    ...graph.nodes.map((n) => `${ids.get(n.id)} [id=${quote(n.id)}, width=${inch(n.width)}, height=${inch(n.height)}];`),
    ...graph.edges.map((e) => `${ids.get(ports.get(e.sourcePortId).nodeId)} -> ${ids.get(ports.get(e.targetPortId).nodeId)} [id=${quote(e.id)}, minlen=${e.minRankSpan}, weight=${e.weight ?? 1}];`), '}'].join('\n');
}

function collinearCubic(points) {
  const a = points[0], b = points[3], vx = b[0] - a[0], vy = b[1] - a[1], length2 = vx * vx + vy * vy;
  if (length2 < 1e-12) return points.every((p) => Math.hypot(p[0] - a[0], p[1] - a[1]) < 1e-8);
  return points.slice(1, 3).every((p) => {
    const dot = (p[0] - a[0]) * vx + (p[1] - a[1]) * vy;
    return Math.abs((p[0] - a[0]) * vy - (p[1] - a[1]) * vx) <= .05 * Math.max(1, Math.sqrt(length2)) && dot >= -.05 && dot <= length2 + .05;
  });
}

export function fromDot(graph, output, inputDigest) {
  const box = output._draw_?.find((op) => op.op === 'P')?.points;
  const bounds = box ? [Math.min(...box.map((p) => p[0])), Math.min(...box.map((p) => p[1])), Math.max(...box.map((p) => p[0])), Math.max(...box.map((p) => p[1]))] : output.bb.split(',').map(Number);
  const height = bounds[3] / SCALE;
  const point = (p) => ({ x: p[0] / SCALE, y: height - p[1] / SCALE });
  const originals = new Map(graph.nodes.map((n, i) => [`n${i}`, n]));
  const nodes = (output.objects ?? []).map((n) => {
    const original = originals.get(n.name); if (!original) throw new Error('dot returned an unknown or compound object');
    const shape = n._draw_?.find((op) => op.op === 'p' || op.op === 'P');
    if (!shape) throw new Error(`dot node ${n.name} has no rectangular geometry`);
    const xs = shape.points.map((p) => p[0] / SCALE), ys = shape.points.map((p) => height - p[1] / SCALE);
    return { id: original.id, x: Math.min(...xs), y: Math.min(...ys), width: Math.max(...xs) - Math.min(...xs), height: Math.max(...ys) - Math.min(...ys) };
  });
  const specs = new Map(graph.edges.map((e) => [e.id, e])), portSpecs = new Map(graph.nodes.flatMap((n) => n.ports.map((p) => [p.id, p]))), ports = [];
  const byGvid = new Map((output.objects ?? []).map((n) => [n._gvid, originals.get(n.name)?.id]));
  const edges = (output.edges ?? []).map((edge) => {
    const spec = specs.get(edge.id); if (!spec) throw new Error('dot returned an unknown incidence');
    if (byGvid.get(edge.tail) !== portSpecs.get(spec.sourcePortId).nodeId || byGvid.get(edge.head) !== portSpecs.get(spec.targetPortId).nodeId) throw new Error('dot changed an incidence source or target');
    const draw = edge._draw_?.filter((op) => op.op === 'b' || op.op === 'L') ?? [];
    if (draw.length !== 1) throw new Error('dot emitted multiple disconnected or unsupported edge shapes');
    let raw = draw[0].points;
    if (draw[0].op === 'b') {
      if ((raw.length - 1) % 3) throw new Error('invalid dot cubic structure');
      const polyline = [raw[0]];
      for (let i = 0; i + 3 < raw.length; i += 3) {
        if (!collinearCubic(raw.slice(i, i + 4))) throw new Error('dot polyline profile emitted a nonlinear cubic; no sampled approximation is substituted');
        polyline.push(raw[i + 3]);
      }
      raw = polyline;
    }
    const points = raw.map(point), arrow = edge._hdraw_?.find((op) => op.op === 'P');
    if (arrow?.points.length !== 3) throw new Error('dot incidence lacks the pinned normal arrow polygon');
    const target = point(arrow.points[1]);
    if (Math.hypot(target.x - points.at(-1).x, target.y - points.at(-1).y) > 1e-8) points.push(target);
    for (const [id, p] of [[spec.sourcePortId, points[0]], [spec.targetPortId, points.at(-1)]]) ports.push({ ...p, id, nodeId: portSpecs.get(id).nodeId });
    return { id: spec.id, sections: [{ id: `${spec.id}:dot`, points, nextSectionIds: [], terminalTargetPortId: spec.targetPortId }] };
  });
  return quantizeGeometry({ schemaVersion: 1, engineVersion: `development-graphviz-${COMPARATOR_PINS.graphviz}`, profileId: 'dot-polyline-equal-size-v1', inputDigest,
    bounds: { x: bounds[0] / SCALE, y: 0, width: (bounds[2] - bounds[0]) / SCALE, height }, nodes, ports, edges });
}

export function toElk(graph) {
  return { id: 'lax-comparator', layoutOptions: { 'elk.algorithm': 'layered', 'elk.direction': 'UP', 'elk.edgeRouting': 'ORTHOGONAL',
    'elk.randomSeed': '1', 'elk.spacing.nodeNode': '28', 'elk.spacing.edgeEdge': '8', 'elk.spacing.portPort': '8',
    'elk.layered.spacing.nodeNodeBetweenLayers': '32', 'elk.layered.mergeEdges': 'false', 'elk.layered.mergeHierarchyEdges': 'false', 'elk.padding': '[top=24,left=24,bottom=24,right=24]' },
    children: graph.nodes.map((n) => {
      const mode = n.ports[0]?.mode ?? 'free-on-side';
      const sides = ['north', 'east', 'south', 'west'];
      const clockwise = [...n.ports].sort((a, b) => sides.indexOf(a.side) - sides.indexOf(b.side) ||
        (a.side === 'south' || a.side === 'west' ? -1 : 1) * ((a.order ?? 0) - (b.order ?? 0)) || (a.id < b.id ? -1 : 1));
      return { id: n.id, width: n.width, height: n.height,
        layoutOptions: { 'elk.portConstraints': { 'free-on-side': 'FIXED_SIDE', 'fixed-order': 'FIXED_ORDER', 'fixed-position': 'FIXED_POS' }[mode], 'elk.nodeSize.constraints': '[]' },
        ports: n.ports.map((p) => ({ id: p.id, width: 0, height: 0, ...(p.offset ? { x: p.offset.x, y: p.offset.y } : {}),
          layoutOptions: { 'elk.port.side': p.side.toUpperCase(), ...(mode === 'fixed-order' ? { 'elk.port.index': String(clockwise.findIndex((q) => q.id === p.id)) } : {}) } })) };
    }), edges: graph.edges.map((e) => ({ id: e.id, sources: [e.sourcePortId], targets: [e.targetPortId] })) };
}

export function fromElk(graph, output, inputDigest) {
  const nodes = (output.children ?? []).map((n) => ({ id: n.id, x: n.x, y: n.y, width: n.width, height: n.height }));
  const ports = (output.children ?? []).flatMap((n) => (n.ports ?? []).map((p) => ({ id: p.id, nodeId: n.id, x: n.x + p.x + p.width / 2, y: n.y + p.y + p.height / 2 })));
  const specs = new Map(graph.edges.map((e) => [e.id, e]));
  const edges = (output.edges ?? []).map((edge) => {
    const spec = specs.get(edge.id); if (!spec || edge.sources?.length !== 1 || edge.targets?.length !== 1 || edge.sources[0] !== spec.sourcePortId || edge.targets[0] !== spec.targetPortId) throw new Error('ELK changed incidence identity or attachments');
    if (edge.sections?.length !== 1) throw new Error('flat ELK comparator requires one complete route section; no section is dropped');
    const section = edge.sections[0];
    return { id: edge.id, sections: [{ id: section.id, points: [section.startPoint, ...(section.bendPoints ?? []), section.endPoint], nextSectionIds: [], terminalTargetPortId: spec.targetPortId }] };
  });
  return quantizeGeometry({ schemaVersion: 1, engineVersion: `development-elkjs-${COMPARATOR_PINS.elkjs}`, profileId: 'elk-orthogonal-equal-size-v1', inputDigest,
    bounds: { x: 0, y: 0, width: output.width, height: output.height }, nodes, ports, edges });
}

export async function runBaselines(options = {}) {
  const inputDir = path.resolve(options.input ?? '/tmp/lax-graph-evidence/benchmark/graphs'), out = path.resolve(options.out ?? '/tmp/lax-graph-evidence/comparators');
  fs.mkdirSync(out, { recursive: true });
  const reportAssets = copyGraphReportAssets(out);
  const requested = options.engine ?? 'graphviz';
  if (!['graphviz', 'elkjs', 'both'].includes(requested)) throw new Error('--engine must be graphviz, elkjs or both');
  const engines = requested === 'both' ? ['graphviz', 'elkjs'] : [requested], hosts = {};
  if (engines.includes('graphviz')) {
    const command = options.dot ?? 'dot', version = spawnSync(command, ['-V'], { encoding: 'utf8' });
    const text = `${version.stdout ?? ''}${version.stderr ?? ''}`.trim();
    if (version.error || version.status !== 0 || !new RegExp(`graphviz version ${COMPARATOR_PINS.graphviz.replaceAll('.', '\\.')}(?:\\s|$)`).test(text)) hosts.graphviz = { unavailable: `Expected Graphviz ${COMPARATOR_PINS.graphviz}: ${version.error?.message ?? text}` };
    else hosts.graphviz = { command, version: text };
  }
  if (engines.includes('elkjs')) {
    try {
      if (!options.elk) throw new Error('Supply --elk with an externally provisioned elkjs package directory; this script never downloads an engine');
      const directory = fs.realpathSync(options.elk), root = fs.realpathSync(path.resolve(path.dirname(new URL(import.meta.url).pathname), '..'));
      if (directory === root || directory.startsWith(root + path.sep)) throw new Error('ELK must be outside the website repository and its dependency tree');
      const pkg = JSON.parse(fs.readFileSync(path.join(directory, 'package.json'), 'utf8'));
      if (pkg.name !== 'elkjs' || pkg.version !== COMPARATOR_PINS.elkjs) throw new Error(`Expected elkjs ${COMPARATOR_PINS.elkjs}`);
      const bundle = path.join(directory, 'lib/elk.bundled.js'), module = await import(pathToFileURL(bundle).href);
      hosts.elkjs = { instance: new module.default(), version: pkg.version, bundleSha256: digest(fs.readFileSync(bundle, 'utf8')) };
    } catch (error) { hosts.elkjs = { unavailable: error.message }; }
  }
  const files = fs.readdirSync(inputDir).filter((f) => f.endsWith('.input.json')).sort();
  const selected = options.limit ? files.slice(0, options.limit) : files;
  const rows = [], timings = [];
  for (let i = 0; i < selected.length; i++) {
    const file = selected[i], id = file.slice(0, -'.input.json'.length), input = JSON.parse(fs.readFileSync(path.join(inputDir, file), 'utf8'));
    for (const engine of engines) {
      const row = { id, engine, metricsVersion: METRICS_VERSION, pin: COMPARATOR_PINS[engine], inputDigest: input.inputDigest,
        cohort: input.fixture?.cohort ?? (id.startsWith('example-') ? 'test-example' : 'archive'), split: input.fixture?.split ?? null, kind: input.fixture?.kind ?? input.display?.kind ?? null,
        nodes: input.graph.nodes.length, edges: input.graph.edges.length, ports: input.graph.nodes.reduce((n, v) => n + v.ports.length, 0) };
      const started = performance.now();
      try {
        const reasons = unsupportedReasons(input.graph, engine);
        if (reasons.length) { row.status = 'unsupported'; row.reasons = reasons; }
        else if (hosts[engine].unavailable) { row.status = 'unavailable'; row.reasons = [hosts[engine].unavailable]; }
        else {
          let raw, geometry;
          if (engine === 'graphviz') {
            const dot = toDot(input.graph); fs.writeFileSync(path.join(out, `${id}.dot`), dot);
            const result = spawnSync(hosts.graphviz.command, ['-Tjson'], { input: dot, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, timeout: 60_000 });
            if (result.error || result.status !== 0) { const error = new Error(result.error?.message ?? result.stderr ?? `dot exited ${result.status}`);
              if (/larger than maximum 65535 allowed/.test(result.stderr ?? '')) error.code = 'dot-scaled-coordinate-limit'; throw error; }
            row.warnings = result.stderr.trim(); raw = JSON.parse(result.stdout); write(path.join(out, `${id}.graphviz.raw.json`), raw);
            geometry = fromDot(input.graph, raw, input.inputDigest);
          } else {
            const request = toElk(input.graph); write(path.join(out, `${id}.elkjs.input.json`), request);
            raw = await hosts.elkjs.instance.layout(request); write(path.join(out, `${id}.elkjs.raw.json`), raw);
            geometry = fromElk(input.graph, raw, input.inputDigest);
          }
          const checked = validateGeometry(input.graph, geometry);
          row.status = checked.valid ? 'valid' : 'contract-defects'; row.metrics = checked.metrics; row.diagnostics = checked.diagnostics;
          row.equalSizesAndIncidences = !checked.diagnostics.some((d) => ['node-size', 'node-roundtrip', 'port-roundtrip', 'edge-roundtrip', 'missing-node', 'missing-port', 'missing-edge', 'fixed-port', 'port-order'].includes(d.code));
          write(path.join(out, `${id}.${engine}.geometry.json`), geometry);
          if (checked.valid && input.drawings) {
            const svg = graphSvg({ graph: input.graph, display: input.display, drawings: new Map(input.drawings) }, geometry, `${id}-${engine}`);
            fs.writeFileSync(path.join(out, `${id}.${engine}.svg`), svg); row.svg = `${id}.${engine}.svg`;
            fs.writeFileSync(path.join(out, `${id}.${engine}.html`), graphReportPage(svg, `${id} ${engine}`, 'assets/')); row.page = `${id}.${engine}.html`;
          }
        }
      } catch (error) { row.status = error.code === 'dot-scaled-coordinate-limit' ? 'unsupported' : 'failed'; row.diagnostics = diagnosticsOf(error); }
      timings.push({ id, engine, elapsedMs: performance.now() - started }); rows.push(row);
    }
    if ((i + 1) % 100 === 0 || i + 1 === selected.length) console.log(`${i + 1}/${selected.length} comparator inputs processed`);
  }
  const manifest = { schemaVersion: 1, comparatorPins: COMPARATOR_PINS, metricsVersion: METRICS_VERSION, reportAssets,
    sourceGraphFiles: files.length, comparedGraphFiles: selected.length, fullPreparedInputSet: files.length === selected.length,
    hosts: Object.fromEntries(Object.entries(hosts).map(([name, host]) => [name, { version: host.version ?? null, unavailable: host.unavailable ?? null, bundleSha256: host.bundleSha256 ?? null }])),
    limitations: ['Prepared inputs that failed the custom benchmark must be supplied separately; prepared-input coverage is not asserted to equal the frozen corpus.',
      'dot uses scaled integer points to retain measured node sizes, polyline routing, and uncoalesced incidences. Unsupported fixed ports/groups are explicit.',
      'No comparator geometry is repaired, shortcut, scaled down for appearance, or accepted by the production renderer. All strict-contract defects remain in rows.',
      'Graphviz line geometry is extended to its actual arrow tip to recover terminal attachment; nonlinear cubics under the polyline profile are rejected.',
      'Comparator runs are development artifacts; neither engine enters a normal build or a public browser dependency.'] };
  write(path.join(out, 'manifest.json'), manifest); write(path.join(out, 'rows.json'), rows);
  fs.writeFileSync(path.join(out, 'index.html'), `<!doctype html><meta charset="utf-8"><title>Optional comparator evidence</title><h1>Optional comparator evidence</h1><p>Only validated diagrams are linked as rendered pages, with report-local fonts/CSS at 100% scale. All defects and unsupported cases remain in <a href="rows.json">the complete rows</a>.</p>${rows.map((r) => `<p>${r.id} ${r.engine}: ${r.status}${r.page ? ` <a href="${r.page}">Rendered graph</a> <a href="${r.svg}">SVG source</a>` : ''}</p>`).join('')}`);
  write(path.join(out, 'performance.json'), { measuredAtUtc: new Date().toISOString(), phases: Object.fromEntries(engines.map((e) => [e, distribution(timings.filter((t) => t.engine === e).map((t) => t.elapsedMs))])), timings });
  console.log(JSON.stringify(Object.fromEntries(engines.map((e) => [e, Object.fromEntries([...new Set(rows.filter((r) => r.engine === e).map((r) => r.status))].map((s) => [s, rows.filter((r) => r.engine === e && r.status === s).length]))]))));
  return { manifest, rows };
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const options = {}, keys = { '--input': 'input', '--out': 'out', '--engine': 'engine', '--dot': 'dot', '--elk': 'elk', '--limit': 'limit' };
  for (let i = 2; i < process.argv.length; i++) { const key = keys[process.argv[i]], value = process.argv[++i]; if (!key || !value) throw new Error('usage: node scripts/graph-baselines.mjs [--input DIR] [--out DIR] [--engine graphviz|elkjs|both] [--elk EXTERNAL_PACKAGE_DIR]'); options[key] = key === 'limit' ? Number(value) : value; }
  const result = await runBaselines(options);
  if (result.rows.some((r) => r.status === 'failed' || r.status === 'unavailable')) process.exitCode = 1;
}
