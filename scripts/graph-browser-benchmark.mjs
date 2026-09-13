// Development evidence only: static SVGs are replayed at equal zoom and body
// label size. Old dock numerals retain their original 7.5px monospace style;
// new measured numerals use 12px regular. No public asset imports this script.
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { gzipSync } from 'node:zlib';
import { chromium } from 'playwright-core';
import { graphInteractionPayload } from '../dist/sitegen/graph-svg.js';
import { graphExpandButton } from '../dist/sitegen/pages/shared.js';
import { PINNED_GRAPH_BROWSER_VERSION } from '../dist/sitegen/graph-measure.js';

const args = process.argv.slice(2);
const option = (key, fallback) => args.includes(key) ? args[args.indexOf(key) + 1] : fallback;
const benchmark = path.resolve(option('--benchmark', '/tmp/lax-graph-evidence/benchmark'));
const before = path.resolve(option('--before', '/tmp/lax-graph-evidence/before'));
const out = path.resolve(option('--out', '/tmp/lax-graph-evidence/browser'));
const assetRoot = path.resolve('assets/site');
const katexCss = createRequire(import.meta.url).resolve('katex/dist/katex.min.css');
const katexRoot = path.dirname(katexCss);
const rows = fs.readFileSync(path.join(benchmark, 'rows.jsonl'), 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse);
let selected = rows.filter((row) => row.status === 'valid');
// This declared runtime tier is independent of observed timings: every proof
// network, every synthetic fixture, and the largest SVG of each graph kind.
// Complete per-view geometry and regression reports remain in the benchmark.
if (args.includes('--interaction-tier')) {
  const tier = new Set(selected.filter((row) => row.kind === 'proofs' || row.cohort === 'test-example').map((row) => row.id));
  for (const kind of ['concepts', 'proofs', 'submissions']) {
    const largest = selected.filter((row) => row.kind === kind).sort((a, b) => b.after.svgElements - a.after.svgElements)[0];
    if (largest) tier.add(largest.id);
  }
  selected = selected.filter((row) => tier.has(row.id));
}
if (option('--limit')) selected = selected.slice(0, Number(option('--limit')));
if (option('--id')) selected = selected.filter((row) => row.id === option('--id'));
const percentile = (values, fraction) => values.length ? [...values].sort((a, b) => a - b)[Math.max(0, Math.ceil(values.length * fraction) - 1)] : null;
const distribution = (values) => ({ n: values.length, p50: percentile(values, .5), p95: percentile(values, .95), max: values.length ? Math.max(...values) : null });
const json = (value) => JSON.stringify(value).replace(/</g, '\\u003c');
const escape = (value) => String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('"', '&quot;');
fs.mkdirSync(out, { recursive: true });
fs.writeFileSync(path.join(out, 'rows.jsonl'), '');

function harness(row, variant) {
  const id = { concepts: 'concept-dag', proofs: 'proof-network', submissions: 'submission-dag' }[row.kind];
  const svg = fs.readFileSync(variant === 'before' ? path.join(before, `${row.id}.svg`) : path.join(benchmark, 'graphs', `${row.id}.svg`), 'utf8');
  const measured = JSON.parse(fs.readFileSync(path.join(benchmark, 'graphs', `${row.id}.input.json`), 'utf8'));
  const interaction = variant === 'after' ? graphInteractionPayload({ ...measured, drawings: new Map() }) : { nodes: {} };
  const prepared = { [id]: { initial: 'default', ancestors: 0, descendants: 0,
    views: { default: { interaction, height: 720, status: '' } } } };
  // The same 720px camera and 1280x900 viewport are used for both stored SVGs.
  // Insets/labels are actual diagram units, never fitted or scaled down.
  return `<!doctype html><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; script-src 'self'; style-src 'self' 'unsafe-inline'; font-src 'self'; img-src 'self'; connect-src 'self'"><link rel="stylesheet" href="assets/katex.css"><link rel="stylesheet" href="assets/style.css"><figure class="graph-figure${row.kind === 'proofs' ? ' proof-network-figure' : ''}">${graphExpandButton('Graph')}<div id="${id}" class="figure-container" data-graph="${row.kind}" style="height:720px">${svg}</div><div class="graph-tooltip" hidden></div></figure><script type="application/json" id="graph-data">${json({ prepared })}</script>${variant === 'after' ? '<script src="assets/graph-interaction.js"></script>' : ''}`;
}
const browser = await chromium.launch({ executablePath: process.env.GRAPH_CHROME ?? '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox', '--font-render-hinting=none'] });
const results = [], errors = [];
let current;
try {
  if (browser.version() !== PINNED_GRAPH_BROWSER_VERSION) throw new Error(`Browser evidence requires ${PINNED_GRAPH_BROWSER_VERSION}; received ${browser.version()}`);
  const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, deviceScaleFactor: 1, reducedMotion: 'reduce', locale: 'en-US', timezoneId: 'UTC' });
  await context.route('**/*', async (route) => {
    const url = new URL(route.request().url());
    if (url.origin !== 'https://graph-evidence.test') return route.abort();
    if (url.pathname === '/fixture.html') return route.fulfill({ contentType: 'text/html', body: harness(current.row, current.variant) });
    if (url.pathname.startsWith('/assets/')) {
      const relative = url.pathname.slice('/assets/'.length);
      let file = path.resolve(assetRoot, relative);
      if (!file.startsWith(assetRoot + path.sep)) return route.abort();
      if (relative === 'katex.css') file = katexCss;
      else if (!fs.existsSync(file) && /^fonts\/KaTeX_[A-Za-z0-9_-]+\.woff2$/u.test(relative)) file = path.join(katexRoot, relative);
      if (!fs.existsSync(file)) return route.abort();
      return route.fulfill({ body: fs.readFileSync(file), contentType: { '.css': 'text/css', '.js': 'text/javascript', '.woff2': 'font/woff2' }[path.extname(file)] ?? 'application/octet-stream' });
    }
    return route.abort();
  });
  const page = await context.newPage();
  const cdp = await context.newCDPSession(page);
  await page.addInitScript(() => {
    window.graphShifts = [];
    new PerformanceObserver((list) => {
      for (const entry of list.getEntries()) if (!entry.hadRecentInput && entry.sources.some((source) => source.node?.closest?.('.graph-figure')))
        window.graphShifts.push(entry.value);
    }).observe({ type: 'layout-shift', buffered: true });
  });
  page.on('pageerror', (error) => errors.push({ id: current?.row.id, variant: current?.variant, message: error.message }));
  for (const row of selected) {
    const result = { id: row.id, kind: row.kind, cohort: row.cohort, split: row.split, svgElements: row.after.svgElements, screens: [] };
    for (const variant of ['before', 'after']) {
      if (variant === 'before' && !fs.existsSync(path.join(before, `${row.id}.svg`))) continue;
      current = { row, variant };
      await page.setViewportSize({ width: 1280, height: 900 });
      await page.goto('https://graph-evidence.test/fixture.html', { waitUntil: 'load' });
      await page.evaluate(() => document.fonts.ready);
      await page.evaluate(() => { const c = document.querySelector('.figure-container'); c.scrollTop = 0; c.scrollLeft = Math.max(0, (c.scrollWidth - c.clientWidth) / 2); });
      await page.screenshot({ path: path.join(out, `${row.id}-${variant}.png`) });
      result.screens.push(`${row.id}-${variant}.png`);
      if (variant !== 'after') continue;
      result.navigation = await page.evaluate(() => {
        const n = performance.getEntriesByType('navigation')[0];
        const paints = Object.fromEntries(performance.getEntriesByType('paint').map((entry) => [entry.name, entry.startTime]));
        return { domInteractiveMs: n.domInteractive - n.startTime,
          domContentLoadedMs: n.domContentLoadedEventEnd - n.startTime, loadMs: n.loadEventEnd - n.startTime,
          firstPaintMs: paints['first-paint'] ?? null, firstContentfulPaintMs: paints['first-contentful-paint'] ?? null,
          graphLayoutShift: window.graphShifts.reduce((sum, value) => sum + value, 0),
          resources: performance.getEntriesByType('resource').map((r) => ({ name: new URL(r.name).pathname, durationMs: r.duration,
            encodedBodyBytes: r.encodedBodySize, decodedBodyBytes: r.decodedBodySize })) };
      });
      const measure = () => page.evaluate(async () => {
        const svg = document.querySelector('.prepared-graph'), camera = svg.querySelector('[data-graph-camera]');
        const all = [...svg.querySelectorAll('[data-node-id]')], handlers = [], nextPaint = [], frames = [];
        const viewport = document.querySelector('.figure-container').getBoundingClientRect();
        const visible = all.filter((node) => { const r = node.getBoundingClientRect(); return r.bottom > viewport.top && r.top < viewport.bottom && r.right > viewport.left && r.left < viewport.right; });
        // A real inspector includes its permitted HTML and math; the timed
        // dispatch includes highlighting and tooltip handler work together.
        for (let i = 0; i < 30 && visible.length; i++) {
          const node = visible[i % visible.length], started = performance.now();
          node.dispatchEvent(new MouseEvent('mouseenter'));
          handlers.push(performance.now() - started);
          if (i < 5) { await new Promise(requestAnimationFrame); await new Promise(requestAnimationFrame); nextPaint.push(performance.now() - started); }
          node.dispatchEvent(new MouseEvent('mouseleave'));
        }
        let previous;
        for (let i = 0; i < 35; i++) {
          document.querySelector(`[data-graph-zoom="${i % 2 ? 'out' : 'in'}"]`).click();
          const now = await new Promise(requestAnimationFrame);
          if (previous !== undefined) frames.push(now - previous); previous = now;
        }
        document.querySelector('[data-graph-zoom="reset"]').click();
        return { nodes: all.length, visibleNodes: visible.length, handlers, nextPaint, frames,
          cameraOnly: svg === document.querySelector('.prepared-graph') && camera === svg.querySelector('[data-graph-camera]') };
      });
      const measurePan = async () => {
        const point = await page.evaluate(() => {
          const c = document.querySelector('.figure-container').getBoundingClientRect();
          const svg = document.querySelector('.prepared-graph'), s = svg.getBoundingClientRect();
          if (!s.width || !s.height) return null;
          const left = Math.max(0, c.left, s.left), right = Math.min(innerWidth, c.right, s.right);
          const top = Math.max(0, c.top, s.top), bottom = Math.min(innerHeight, c.bottom, s.bottom);
          for (const y of [top + 8, top + 42, bottom - 8]) for (const x of [left + 8, right - 8, (left + right) / 2]) {
            if (x <= left || x >= right || y <= top || y >= bottom) continue;
            const target = document.elementFromPoint(x, y);
            if (target?.closest('svg') === svg && !target.closest('[data-node-id]')) return { x, y };
          }
          throw new Error('No visible graph background for the declared pan trial');
        });
        if (!point) return { frames: [], active: false, skipped: 'empty drawing has no draggable surface' };
        await page.mouse.move(point.x, point.y); await page.mouse.down();
        const result = await page.evaluate(async (point) => {
          const svg = document.querySelector('.prepared-graph'), frames = [];
          let previous;
          for (let i = 0; i < 35; i++) {
            svg.dispatchEvent(new PointerEvent('pointermove', { pointerId: 1, pointerType: 'mouse', buttons: 1,
              clientX: point.x + (i % 2 ? 0 : 4), clientY: point.y + (i % 2 ? 0 : 4) }));
            const now = await new Promise(requestAnimationFrame);
            if (previous !== undefined) frames.push(now - previous); previous = now;
          }
          return { frames, active: svg.classList.contains('graph-dragging') };
        }, point);
        await page.mouse.up();
        await page.locator('[data-graph-zoom="reset"]').click();
        return result;
      };
      // All diagrams get screenshots; the complete declared tier (largest
      // actual view of each kind plus all proof networks) gets interaction.
      if (!args.includes('--screenshots-only') && (row.kind === 'proofs' || row.cohort === 'test-example' || selected.filter((r) => r.kind === row.kind).sort((a, b) => b.after.svgElements - a.after.svgElements)[0]?.id === row.id)) {
        result.desktop = await measure();
        result.desktop.pan = await measurePan();
        await page.setViewportSize({ width: 390, height: 844 });
        await cdp.send('Emulation.setCPUThrottlingRate', { rate: 4 });
        result.mobile4xCpu = await measure();
        result.mobile4xCpu.pan = await measurePan();
        await cdp.send('Emulation.setCPUThrottlingRate', { rate: 1 });
        await page.screenshot({ path: path.join(out, `${row.id}-narrow.png`) });
        result.screens.push(`${row.id}-narrow.png`);
      }
    }
    results.push(result);
    fs.appendFileSync(path.join(out, 'rows.jsonl'), JSON.stringify(result) + '\n');
    if (results.length % 100 === 0 || results.length === selected.length) console.log(`${results.length}/${selected.length} browser comparisons captured`);
  }
  const summary = {};
  for (const name of ['desktop', 'mobile4xCpu']) {
    const measured = results.filter((row) => row[name]);
    const handlers = measured.flatMap((row) => row[name].handlers), paints = measured.flatMap((row) => row[name].nextPaint), frames = measured.flatMap((row) => row[name].frames);
    const panFrames = measured.flatMap((row) => row[name].pan.frames);
    summary[name] = { graphs: measured.length, handlerMs: distribution(handlers), nextPaintMs: distribution(paints), frameMs: distribution(frames),
      panFrameMs: distribution(panFrames), panFramesOver25Ms: panFrames.filter((time) => time > 25).length,
      panInactive: measured.filter((row) => !row[name].pan.active && !row[name].pan.skipped).map((row) => row.id),
      framesOver25Ms: frames.filter((time) => time > 25).length, totalFrames: frames.length };
  }
  const interaction = fs.readFileSync(path.join(assetRoot, 'graph-interaction.js'));
  const forbidden = results.flatMap((r) => (r.navigation?.resources ?? []).filter((resource) =>
    /(?:\/graph-local\/|\/graph-local\.js|\/graph-measure-local\.js|\/layout\.js|\/dag\.js|elk(?:js)?|graphviz|cytoscape|dagre)/iu.test(resource.name)).map((resource) => ({ id: r.id, ...resource })));
  const navigation = {};
  for (const key of ['domInteractiveMs', 'domContentLoadedMs', 'loadMs', 'firstPaintMs', 'firstContentfulPaintMs'])
    navigation[key] = distribution(results.map((r) => r.navigation?.[key]).filter((value) => typeof value === 'number'));
  const report = { schemaVersion: 1, browser: browser.version(), benchmarkManifestSha256: createHash('sha256').update(fs.readFileSync(path.join(benchmark, 'manifest.json'))).digest('hex'),
    scriptSha256: createHash('sha256').update(fs.readFileSync(new URL(import.meta.url))).digest('hex'),
    reference: { cpu: os.cpus()[0].model, logicalCpus: os.cpus().length, os: `${os.type()} ${os.release()}`, node: process.version },
    viewport: { desktop: { width: 1280, height: 900 }, narrow: { width: 390, height: 844 }, deviceScaleFactor: 1 },
    conditions: 'Headless Chromium, reduced motion, actual graph and KaTeX styles/fonts; narrow viewport with 4x CPU throttling approximates load, not physical mobile hardware. Host load recorded externally. Next-paint latency is a double-rAF proxy, not a compositor measurement. Frame intervals are observed rAF intervals; >25ms is a missed 60Hz-frame indicator. Pan uses an actual mouse press and scripted pointer moves at rAF cadence; touch scrolling is covered separately by integration tests.',
    screenshots: 'Stored whole-output SVG, 100% graph zoom, 12px body labels, equal 720px viewport, top and horizontally centered; old dock numerals retain 7.5px monospace versus 12px regular measured numerals. Screenshots intentionally show the viewport, not a shrunken fit of the whole diagram.',
    coverage: { preparedViews: rows.length, capturedViews: results.length,
      policy: args.includes('--interaction-tier') ? 'All proof networks, all synthetic fixtures, largest SVG element count of each kind; chosen before timing.' : 'All valid views unless explicitly restricted by --id or --limit.' },
    graphs: results.length, errors, publicInteractionBytes: interaction.length, publicInteractionGzipBytes: gzipSync(interaction, { level: 9 }).length,
    thirdPartyGraphBytes: forbidden.length ? null : 0, publicLayoutSearchBytes: forbidden.length ? null : 0, forbiddenGraphResources: forbidden,
    navigation,
    graphLayoutShift: distribution(results.filter((r) => r.navigation).map((r) => r.navigation.graphLayoutShift)), summary };
  fs.writeFileSync(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  fs.writeFileSync(path.join(out, 'index.html'), `<!doctype html><meta charset="utf-8"><title>Graph comparison gallery</title><style>body{font-family:serif;max-width:1300px;margin:auto}img{max-width:100%;height:auto}summary{cursor:pointer}figure{margin:0}button{font:inherit}</style><h1>Equal-scale graph comparisons</h1><p>100% zoom; 12px body labels; 1280×900 viewport. Old dock numerals retain their original 7.5px monospace style; new measured numerals use 12px regular text. Complete before/after SVGs and per-graph geometry metrics accompany this gallery. The viewport is centered at the top of each graph.</p><p><a href="report.json">Measured browser report</a></p>${results.map((r) => `<details><summary>${escape(r.kind)} ${escape(r.split)} ${escape(r.id)}</summary>${r.screens.map((file) => `<figure><figcaption>${file.endsWith('-before.png') ? 'Before' : file.endsWith('-narrow.png') ? 'After, narrow viewport' : 'After'}</figcaption><img loading="lazy" src="${file}" width="${file.endsWith('-narrow.png') ? '390' : '1280'}" height="${file.endsWith('-narrow.png') ? '844' : '900'}"></figure>`).join('')}</details>`).join('')}`);
  console.log(JSON.stringify(report, null, 2));
} finally { await browser.close(); }
