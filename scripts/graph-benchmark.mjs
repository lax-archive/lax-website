// Development-only full-corpus evidence. No generator, browser asset, layout
// library or database write imports this script. Build dist before invoking.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { performance } from 'node:perf_hooks';
import { gzipSync } from 'node:zlib';
import { pathToFileURL, fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';
import { canonical, digest } from './graph-inventory.mjs';
import { distribution, graphStatistics, METRICS_VERSION, metricComparison, oldOutputMetrics, visibleContentBounds } from './graph-metrics.mjs';
import { copyGraphReportAssets, graphReportPage } from './graph-report-assets.mjs';
import { layoutGraph, DEFAULT_PROFILE, ENGINE_VERSION, SELECTION_POLICY } from '../dist/graph-layout/index.js';
import { canonicalJson } from '../dist/graph-layout/normalize.js';
import { quantizeGeometry, pathData, polylineCommands } from '../dist/graph-layout/geometry.js';
import { parsePathData, validateGeometry } from '../dist/graph-layout/validate.js';
import { projectGraph, measureDisplayGraph } from '../dist/sitegen/graph-project.js';
import { displayLabelRequests } from '../dist/sitegen/graph-node-size.js';
import { createGraphMeasurer } from '../dist/sitegen/graph-measure.js';
import { graphSvg } from '../dist/sitegen/graph-svg.js';

const repository = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const write = (file, value) => { fs.mkdirSync(path.dirname(file), { recursive: true }); fs.writeFileSync(file, canonical(value) + '\n'); };
const diagnosticsOf = (error) => error?.diagnostics ?? [{ code: error?.code ?? error?.name ?? 'benchmark-error', message: String(error?.message ?? error) }];
const timed = (timings, name, operation) => { const start = performance.now(); try { return operation(); } finally { timings[name] = (timings[name] ?? 0) + performance.now() - start; } };
const safeGit = (args) => { try { return execFileSync('git', args, { cwd: repository, encoding: 'utf8' }).trim(); } catch { return null; } };
const escape = (s) => String(s).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('"', '&quot;');

export function checkedFinalGeometry(graph, input) {
  const geometry = quantizeGeometry(input);
  const serialized = { ...geometry, edges: geometry.edges.map((e) => ({ ...e, sections: e.sections.map((s) => ({ ...s,
    commands: parsePathData(pathData(s.commands ?? polylineCommands(s.points))) })) })) };
  const checked = validateGeometry(graph, serialized);
  if (!checked.valid) { const error = new Error('Independent serialized geometry validation failed'); error.diagnostics = checked.diagnostics; throw error; }
  return { geometry: serialized, metrics: checked.metrics };
}

export function layoutInputDigest(measured, labels, environment, profile = DEFAULT_PROFILE) {
  return digest({ graph: measured.graph, kind: measured.display.kind,
    labels: displayLabelRequests([measured.display]).map(({ text }) => [text, labels.get(text).signature]),
    measurementSignature: environment.signature, engineVersion: ENGINE_VERSION, profile, selectionPolicy: SELECTION_POLICY });
}

export async function prepareBenchmarkInputs(fixtures, options = {}) {
  const started = performance.now(), projected = fixtures.map((fixture) => {
    const timings = {};
    try { return { fixture, display: timed(timings, 'projection', () => projectGraph(fixture.kind, fixture.data)), timings }; }
    catch (error) { return { fixture, diagnostics: diagnosticsOf(error), timings }; }
  });
  const requests = displayLabelRequests(projected.flatMap((entry) => entry.display ? [entry.display] : []));
  const measurer = createGraphMeasurer({ cacheDir: options.measurementCache });
  let metrics;
  try { metrics = await measurer.measureLabels(requests); }
  finally { await measurer.close(); }
  const labels = new Map(requests.map(({ text }, i) => [text, metrics[i]]));
  for (const entry of projected) if (entry.display) {
    try {
      entry.measured = timed(entry.timings, 'nodeSizing', () => measureDisplayGraph(entry.display, labels, (options.profile ?? DEFAULT_PROFILE).portSeparation));
      entry.inputDigest = layoutInputDigest(entry.measured, labels, measurer.environment, options.profile);
    } catch (error) { entry.diagnostics = diagnosticsOf(error); }
  }
  return { entries: projected, measurement: measurer.statistics, environment: measurer.environment, elapsedMs: performance.now() - started };
}

export function summarizeRows(rows) {
  const summaries = {};
  for (const cohort of ['archive', 'test-example']) for (const split of ['all', 'tuning', 'held-out', 'diagnostic']) {
    const selected = rows.filter((r) => r.cohort === cohort && (split === 'all' || r.split === split));
    if (!selected.length) continue;
    const valid = selected.filter((r) => r.status === 'valid'), comparable = valid.filter((r) => r.comparison?.comparable);
    summaries[`${cohort}:${split}`] = { graphs: selected.length, valid: valid.length, failed: selected.length - valid.length,
      kinds: Object.fromEntries([...new Set(selected.map((r) => r.kind))].sort().map((k) => [k, selected.filter((r) => r.kind === k).length])),
      comparableOldOutputs: comparable.length, incomparableOrMissingOldOutputs: selected.length - comparable.length,
      crossings: distribution(valid.map((r) => r.after.metrics.crossings)),
      width: distribution(valid.map((r) => r.after.metrics.width)), height: distribution(valid.map((r) => r.after.metrics.height)),
      crossingComparison: { better: comparable.filter((r) => r.comparison.deltas.crossings < 0).length,
        equal: comparable.filter((r) => r.comparison.deltas.crossings === 0).length,
        worse: comparable.filter((r) => r.comparison.deltas.crossings > 0).length },
      anyMetricRegression: comparable.filter((r) => r.comparison.regressions.length).length,
      failures: selected.filter((r) => r.status !== 'valid').map((r) => ({ id: r.id, diagnostics: r.diagnostics })) };
  }
  return summaries;
}

function reportMarkdown(manifest, rows, performanceReport) {
  const lines = ['# Frozen graph-corpus comparison', '',
    `Metrics: ${METRICS_VERSION}. Engine: ${ENGINE_VERSION}. Profile: ${manifest.profile.id}. Policy: ${SELECTION_POLICY}.`, '',
    `Selection policy is the frozen initial policy; no corpus parameter tuning was performed. Candidate geometry retention: ${manifest.retainCandidates ? 'enabled; extra development review/validation work is included in these timings' : 'disabled'}.`, '',
    `Archive corpus: ${manifest.archiveGraphCount} / ${manifest.frozenArchiveGraphCount} frozen graphs. Coverage: **${manifest.fullCorpus ? 'complete' : 'explicit subset; not a full-corpus result'}**.`, '',
    `Renderer baseline: ${manifest.rendererRevision}. Database: ${manifest.databaseRevision}. Frozen corpus SHA-256: ${manifest.corpusDigest}.`, '',
    'The tuning/held-out assignment is copied unchanged from the frozen corpus. Synthetic examples are reported separately. Every failed graph, every geometry-cost increase and every defined crossing-angle decrease appears below; no graph is removed to improve an average.', '',
    '| Cohort | Graphs | Valid | Failed | Comparable old output | Crossings better / equal / worse |',
    '| --- | ---: | ---: | ---: | ---: | ---: |'];
  for (const [key, summary] of Object.entries(summarizeRows(rows))) lines.push(`| ${key} | ${summary.graphs} | ${summary.valid} | ${summary.failed} | ${summary.comparableOldOutputs} | ${Object.values(summary.crossingComparison).join(' / ')} |`);
  lines.push('', '## Measured resource results', '', `Host: ${performanceReport.reference.cpu}; ${performanceReport.reference.os}; Node ${performanceReport.reference.node}.`, '',
    `Node process peak RSS: ${performanceReport.nodePeakRssBytes} bytes. This excludes browser and optional comparator child processes.`, '',
    '| Pass | Graphs | Total ms | Geometry hits | Geometry misses | Label hits / misses | Byte mismatches |', '| --- | ---: | ---: | ---: | ---: | ---: | ---: |');
  for (const pass of performanceReport.passes) lines.push(`| ${pass.name} | ${pass.graphs} | ${pass.elapsedMs.toFixed(1)} | ${pass.cacheHits} | ${pass.cacheMisses} | ${pass.measurement.cacheHits} / ${pass.measurement.cacheMisses} | ${pass.byteMismatches.length} |`);
  lines.push('', 'Full per-graph timings and inclusive phase p50/p95/max are in performance.json. The cold pass always computes layout; label cache statistics state whether text measurement was cold. The warm pass independently validates cache contents. Timings and host data never enter geometry bytes.', '',
    'Public transfer, browser paint, interaction latency and mobile responsiveness require the separate browser report; this build benchmark does not claim those targets.', '',
    '## Failures', '');
  const failures = rows.filter((r) => r.status !== 'valid');
  if (!failures.length) lines.push('None.');
  for (const row of failures) lines.push(`- ${row.id} (${row.kind}, ${row.split}): ${row.diagnostics.map((d) => d.code).join(', ')}. Full diagnostics: rows.jsonl.`);
  lines.push('', '## Per-graph regression table', '', 'Deltas are after minus the actual old SVG at the same SVG coordinate scale. Both renderers use 12px body labels; old numbered docks used 7.5px monospace and new docks use measured 12px regular text. The old renderer truncated labels/identifiers while the new renderer wraps complete labels. Measured node dimensions can differ. Baselines with changed incidence multiplicity or unverifiable terminal identity have no numerical improvement verdict.', '',
    '| Graph | Kind / split | Crossing delta | Bend delta | Width delta | Height delta | Minimum angle delta (degrees) | All worsened metrics |', '| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |');
  for (const row of rows.filter((r) => r.comparison?.comparable && r.comparison.regressions.length)) {
    const d = row.comparison.deltas;
    lines.push(`| [${row.id.slice(0, 12)}](graphs/${row.id}.html) | ${row.kind} / ${row.split} | ${d.crossings} | ${d.bends} | ${d.width.toFixed(2)} | ${d.height.toFixed(2)} | ${d.minimumCrossingAngle === null ? 'not comparable' : d.minimumCrossingAngle.toFixed(2)} | ${row.comparison.regressions.join(', ')} |`);
  }
  lines.push('', '## Incomparable baseline cases', '');
  for (const row of rows.filter((r) => r.cohort === 'archive' && !r.comparison?.comparable)) lines.push(`- ${row.id}: ${row.comparison?.reason ?? row.status}; ${row.before?.diagnostics.map((d) => d.code).join(', ') ?? 'baseline unavailable'}.`);
  return lines.join('\n') + '\n';
}

export async function benchmark(options = {}) {
  const corpusFile = path.resolve(options.corpus ?? path.join(repository, 'test/fixtures/graph-layout/corpus.json'));
  const corpusBytes = fs.readFileSync(corpusFile), corpus = JSON.parse(corpusBytes);
  const out = path.resolve(options.out ?? '/tmp/lax-graph-evidence/benchmark'), beforeDir = path.resolve(options.before ?? '/tmp/lax-graph-evidence/before');
  const profile = options.profile ?? DEFAULT_PROFILE;
  fs.mkdirSync(out, { recursive: true });
  const reportAssets = copyGraphReportAssets(out);
  let archive = corpus.graphs.map((g) => ({ ...g, cohort: 'archive' }));
  if (options.id) archive = archive.filter((g) => g.id === options.id);
  if (options.limit !== undefined) archive = archive.slice(0, options.limit);
  const syntheticFile = path.join(repository, 'test/fixtures/graph-layout/diagnostics.json');
  const synthetic = options.noSynthetic ? [] : JSON.parse(fs.readFileSync(syntheticFile, 'utf8')).graphs.map((g) => ({ ...g, id: `example-${g.id}`, split: 'diagnostic', stratum: 'synthetic', cohort: 'test-example' }));
  const fixtures = [...archive, ...synthetic];
  const measurementCache = options.coldLabels ? fs.mkdtempSync(path.join(out, 'cold-labels-')) : path.resolve(options.measurementCache ?? path.join(out, 'labels'));
  const cache = path.join(out, 'geometry-cache'); fs.mkdirSync(cache, { recursive: true });
  const sourceFiles = [...fs.readdirSync(path.join(repository, 'dist/graph-layout')).filter((f) => f.endsWith('.js')).map((f) => `dist/graph-layout/${f}`),
    ...['graph-project', 'graph-node-size', 'graph-measure', 'graph-svg', 'markdown', 'assets'].map((name) => `dist/sitegen/${name}.js`),
    'assets/site/style.css', 'assets/site/graph-measure-local.js', 'assets/site/graph-fonts.json',
    'scripts/graph-benchmark.mjs', 'scripts/graph-metrics.mjs', 'scripts/graph-report-assets.mjs'].sort().map((file) => [file, digest(fs.readFileSync(path.join(repository, file), 'utf8'))]);
  const manifest = { schemaVersion: 1, metricsVersion: METRICS_VERSION, engineVersion: ENGINE_VERSION, profile, selectionPolicy: SELECTION_POLICY,
    corpusDigest: digest(corpusBytes.toString()), rendererRevision: corpus.rendererRevision, databaseRevision: corpus.databaseRevision,
    splitPolicy: corpus.splitPolicy, frozenArchiveGraphCount: corpus.graphs.length, archiveGraphCount: archive.length,
    syntheticGraphCount: synthetic.length, fullCorpus: archive.length === corpus.graphs.length, retainCandidates: options.retainCandidates !== false,
    graphIds: fixtures.map((g) => g.id), implementationRevision: safeGit(['rev-parse', 'HEAD']),
    sourceFiles, implementationSourceDigest: digest(sourceFiles), reportAssets };
  write(path.join(out, 'manifest.json'), manifest);
  fs.writeFileSync(path.join(out, 'rows.jsonl'), ''); fs.writeFileSync(path.join(out, 'performance.jsonl'), '');
  const rows = [], canonicalHashes = new Map(), performanceRows = [], passes = [];
  let measurementProvider;
  for (const passName of ['cold', 'warm']) {
    const passStarted = performance.now();
    const prepared = await prepareBenchmarkInputs(fixtures, { measurementCache, profile });
    measurementProvider = prepared.environment.providerId;
    manifest.measurementSignature = prepared.environment.signature; manifest.measurementProvider = measurementProvider;
    write(path.join(out, 'manifest.json'), manifest);
    write(path.join(out, 'measurement-environment.json'), prepared.environment);
    const pass = { name: passName, graphs: fixtures.length, cacheHits: 0, cacheMisses: 0, corruptEntries: 0,
      measurement: prepared.measurement, preparationMs: prepared.elapsedMs, byteMismatches: [], elapsedMs: 0 };
    let failures = 0;
    for (let i = 0; i < prepared.entries.length; i++) {
      const entry = prepared.entries[i], fixture = entry.fixture, timings = { ...entry.timings }, start = performance.now();
      const row = { schemaVersion: 1, metricsVersion: METRICS_VERSION, id: fixture.id, kind: fixture.kind, state: fixture.state ?? 'default',
        cohort: fixture.cohort, split: fixture.split, stratum: fixture.stratum, splitGroup: fixture.splitGroup ?? null,
        occurrences: fixture.occurrences ?? [], status: 'failed', diagnostics: entry.diagnostics ?? [] };
      let cacheStatus = 'not-attempted';
      if (passName === 'cold' && fixture.cohort === 'archive') {
        try { row.before = timed(timings, 'oldOutputValidation', () => oldOutputMetrics(fixture, JSON.parse(fs.readFileSync(path.join(beforeDir, fixture.id + '.json'), 'utf8')))); }
        catch (error) { row.before = { diagnostics: diagnosticsOf(error), comparableIncidences: false }; }
      }
      try {
        if (!entry.measured) { const error = new Error('Projection or measurement failed'); error.diagnostics = row.diagnostics; throw error; }
        const graph = entry.measured.graph, cacheFile = path.join(cache, entry.inputDigest + '.json');
        if (passName === 'cold') write(path.join(out, 'graphs', fixture.id + '.input.json'), { inputDigest: entry.inputDigest, graph, display: entry.measured.display, drawings: [...entry.measured.drawings],
          fixture: { id: fixture.id, kind: fixture.kind, cohort: fixture.cohort, split: fixture.split, state: fixture.state ?? 'default', stratum: fixture.stratum, splitGroup: fixture.splitGroup ?? null } });
        let result;
        if (passName === 'warm') {
          try {
            const cached = timed(timings, 'cacheRead', () => JSON.parse(fs.readFileSync(cacheFile, 'utf8')));
            if (cached.inputDigest !== entry.inputDigest || cached.payloadDigest !== digest(cached.result)) throw new Error('cache payload digest mismatch');
            timed(timings, 'cacheValidation', () => {
              const checked = checkedFinalGeometry(graph, cached.result.geometry);
              if (canonical(checked.metrics) !== canonical(cached.result.metrics)) throw new Error('cached metrics disagree with geometry');
              for (const candidate of cached.result.candidateGeometries ?? []) checkedFinalGeometry(graph, candidate.geometry);
            });
            result = cached.result; pass.cacheHits++; cacheStatus = 'hit';
          } catch (error) { if (error.code !== 'ENOENT') pass.corruptEntries++; }
        }
        if (!result) {
          pass.cacheMisses++; cacheStatus = 'miss';
          const phaseStarts = new Map();
          result = timed(timings, 'layoutSearch', () => layoutGraph(graph, { inputDigest: entry.inputDigest, profile, retainCandidates: options.retainCandidates !== false,
            onPhase: ({ phase, start: beginning }) => {
              const stack = phaseStarts.get(phase) ?? []; phaseStarts.set(phase, stack);
              if (beginning) stack.push(performance.now());
              else { const opened = stack.pop(); if (opened !== undefined) timings[`core:${phase}`] = (timings[`core:${phase}`] ?? 0) + performance.now() - opened; }
            } }));
          const checked = timed(timings, 'finalValidation', () => checkedFinalGeometry(graph, result.geometry));
          result = { ...result, ...checked };
          timed(timings, 'cacheWrite', () => write(cacheFile, { schemaVersion: 1, inputDigest: entry.inputDigest, payloadDigest: digest(result), result }));
        }
        const bytes = canonicalJson(result.geometry) + '\n', geometryDigest = digest(bytes);
        if (passName === 'cold') canonicalHashes.set(fixture.id, geometryDigest);
        else if (canonicalHashes.get(fixture.id) !== geometryDigest) pass.byteMismatches.push(fixture.id);
        row.status = 'valid'; row.inputDigest = entry.inputDigest; row.diagnostics = result.diagnostics;
        row.statistics = graphStatistics(fixture, entry.measured, result.geometry, result.stats);
        row.after = { metrics: result.metrics, contentBounds: visibleContentBounds(graph, result.geometry),
          geometryDigest, geometryBytes: Buffer.byteLength(bytes), geometryGzipBytes: gzipSync(bytes, { level: 9 }).length,
          search: result.stats, dummyGaps: result.stats.dummyGaps ?? null, permutationTrials: result.stats.permutationTrials ?? null,
          candidates: result.candidates, validator: { valid: true, coordinateQuantum: .001, curveMaximumDeviation: .01 } };
        if (passName === 'cold') {
          const svg = timed(timings, 'svgSerialization', () => graphSvg(entry.measured, result.geometry, fixture.id));
          row.after.svgBytes = Buffer.byteLength(svg); row.after.svgGzipBytes = gzipSync(svg, { level: 9 }).length;
          row.after.svgElements = (svg.match(/<[A-Za-z][\w:-]*(?=[\s>])/g) ?? []).length;
          const graphDir = path.join(out, 'graphs'); fs.mkdirSync(graphDir, { recursive: true });
          fs.writeFileSync(path.join(graphDir, fixture.id + '.geometry.json'), bytes);
          fs.writeFileSync(path.join(graphDir, fixture.id + '.svg'), svg);
          fs.writeFileSync(path.join(graphDir, fixture.id + '.html'), graphReportPage(svg, fixture.id));
          row.after.frontier = timed(timings, 'candidateArchive', () => (result.candidateGeometries ?? []).map((candidate, index) => {
            const checked = checkedFinalGeometry(graph, candidate.geometry), candidateBytes = canonicalJson(checked.geometry) + '\n';
            const prefix = `${fixture.id}.candidate-${index}`, candidateSvg = graphSvg(entry.measured, checked.geometry, `${fixture.id}-candidate-${index}`);
            fs.writeFileSync(path.join(graphDir, prefix + '.geometry.json'), candidateBytes);
            fs.writeFileSync(path.join(graphDir, prefix + '.svg'), candidateSvg);
            fs.writeFileSync(path.join(graphDir, prefix + '.html'), graphReportPage(candidateSvg, candidate.id));
            return { id: candidate.id, geometryDigest: digest(candidateBytes), metrics: checked.metrics, geometry: `graphs/${prefix}.geometry.json`, svg: `graphs/${prefix}.svg`, page: `graphs/${prefix}.html` };
          }));
          row.comparison = metricComparison(row.before, result.metrics);
        }
      } catch (error) {
        failures++; row.status = 'failed'; row.diagnostics = diagnosticsOf(error);
        row.comparison = { comparable: false, reason: 'New graph preparation or layout failed', deltas: null, regressions: [] };
        if (entry.measured) row.statistics = graphStatistics(fixture, entry.measured);
        if (failures <= 10) console.log(`${passName} FAILED ${fixture.id}: ${row.diagnostics.map((d) => d.code).join(', ')}`);
      }
      const perf = { id: fixture.id, kind: fixture.kind, split: fixture.split, cohort: fixture.cohort, pass: passName, status: row.status,
        cache: cacheStatus, elapsedMs: performance.now() - start, phasesMs: timings,
        nodeRssBytes: process.memoryUsage().rss, nodeHeapUsedBytes: process.memoryUsage().heapUsed, nodePeakRssBytes: process.resourceUsage().maxRSS * 1024 };
      performanceRows.push(perf); fs.appendFileSync(path.join(out, 'performance.jsonl'), JSON.stringify(perf) + '\n');
      if (passName === 'cold') { rows.push(row); fs.appendFileSync(path.join(out, 'rows.jsonl'), canonical(row) + '\n'); }
      if ((i + 1) % 100 === 0 || i + 1 === fixtures.length) console.log(`${passName} ${i + 1}/${fixtures.length}, failures=${failures}, cache=${pass.cacheHits}/${pass.cacheMisses}, elapsed=${((performance.now() - passStarted) / 1000).toFixed(1)}s`);
      // Yield between graphs so host controls and progress consumers remain live.
      await new Promise((resolve) => setImmediate(resolve));
    }
    pass.elapsedMs = performance.now() - passStarted; pass.failures = failures; passes.push(pass);
  }
  const performanceReport = { schemaVersion: 1, measuredAtUtc: new Date().toISOString(),
    reference: { cpu: os.cpus()[0]?.model ?? null, logicalCpus: os.cpus().length, os: `${os.type()} ${os.release()} ${os.arch()}`, node: process.version,
      physicalMemoryBytes: os.totalmem(), browser: measurementProvider, conditions: 'desktop Node process; no CPU throttling; filesystem cache and concurrent host load uncontrolled' },
    nodePeakRssBytes: process.resourceUsage().maxRSS * 1024, retainCandidates: options.retainCandidates !== false,
    memoryScope: 'Node process lifetime peak; excludes measurement-browser and optional comparator processes', passes,
    phases: Object.fromEntries(['cold', 'warm'].map((pass) => [pass, Object.fromEntries([...new Set(performanceRows.filter((r) => r.pass === pass).flatMap((r) => Object.keys(r.phasesMs)))].sort().map((phase) => [phase, distribution(performanceRows.filter((r) => r.pass === pass && r.phasesMs[phase] !== undefined).map((r) => r.phasesMs[phase]))]))])),
    phaseAccounting: 'Core phase durations are inclusive and may be nested; do not sum them. Host layoutSearch includes every internal operation and final component packing/validation.',
    rows: performanceRows };
  write(path.join(out, 'summary.json'), summarizeRows(rows)); write(path.join(out, 'performance.json'), performanceReport);
  write(path.join(out, 'failures.json'), rows.filter((r) => r.status !== 'valid'));
  write(path.join(out, 'regressions.json'), rows.filter((r) => r.comparison?.regressions.length));
  fs.writeFileSync(path.join(out, 'report.md'), reportMarkdown(manifest, rows, performanceReport));
  fs.writeFileSync(path.join(out, 'index.html'), `<!doctype html><meta charset="utf-8"><title>Custom graph corpus evidence</title><h1>Custom graph corpus evidence</h1><p>${rows.length} frozen views and separately tagged test examples. <a href="report.md">Complete metrics and regression report</a>. Graph pages carry local fonts/CSS and scroll at 100% scale; raw SVG links are source files.</p>${rows.map((r) => `<p>${escape(r.kind)} ${escape(r.split)} ${r.status === 'valid' ? `<a href="graphs/${r.id}.html">${r.id}</a> (<a href="graphs/${r.id}.svg">SVG source</a>) ${(r.after.frontier ?? []).map((c, i) => `<a href="${c.page}">candidate ${i + 1}</a>`).join(' ')}` : `${r.id}: FAILED`}</p>`).join('')}`);
  console.log(`Evidence written to ${out}; valid=${rows.filter((r) => r.status === 'valid').length}/${rows.length}`);
  return { manifest, rows, performance: performanceReport };
}

function optionsFromArgs(argv) {
  const options = {};
  const keys = { '--corpus': 'corpus', '--before': 'before', '--out': 'out', '--measurement-cache': 'measurementCache', '--id': 'id', '--limit': 'limit' };
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--cold-labels') options.coldLabels = true;
    else if (arg === '--no-retain-candidates') options.retainCandidates = false;
    else if (arg === '--no-synthetic') options.noSynthetic = true;
    else if (keys[arg] && argv[i + 1]) options[keys[arg]] = arg === '--limit' ? Number(argv[++i]) : argv[++i];
    else throw new Error(`Unknown or incomplete argument ${arg}`);
  }
  if (options.limit !== undefined && (!Number.isSafeInteger(options.limit) || options.limit < 1)) throw new Error('--limit must be a positive integer');
  return options;
}
if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const options = optionsFromArgs(process.argv.slice(2));
  try {
    const result = await benchmark(options);
    if (result.rows.some((r) => r.status !== 'valid') || result.performance.passes.some((p) => p.failures || p.byteMismatches.length)) process.exitCode = 1;
  } catch (error) {
    write(path.join(path.resolve(options.out ?? '/tmp/lax-graph-evidence/benchmark'), 'fatal-diagnostics.json'), { status: 'aborted', diagnostics: diagnosticsOf(error) });
    console.error(error); process.exitCode = 1;
  }
}
