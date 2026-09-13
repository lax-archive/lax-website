// Capture the WHOLE old renderer, including its post-layout port selection,
// shortcutting, rounding and casings. No calls into the new layout core.
import fs from 'node:fs';
import path from 'node:path';
import { chromium } from 'playwright-core';

const [corpusFile, oldSite, out] = process.argv.slice(2);
if (!corpusFile || !oldSite || !out) throw new Error('usage: node scripts/graph-baseline-capture.mjs CORPUS OLD_SITE OUT');
const corpus = JSON.parse(fs.readFileSync(corpusFile, 'utf8'));
fs.mkdirSync(out, { recursive: true });
fs.cpSync(path.join(oldSite, 'assets'), path.join(out, 'assets'), { recursive: true });
const browser = await chromium.launch({ executablePath: process.env.GRAPH_CHROME ?? '/usr/bin/google-chrome', headless: true, args: ['--no-sandbox'] });
const rows = [];
try {
  const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, deviceScaleFactor: 1 });
  let current;
  await context.route('**/*', async (route) => {
    const url = new URL(route.request().url());
    if (url.pathname === '/fixture.html') {
      const id = { concepts: 'concept-dag', submissions: 'submission-dag', proofs: 'proof-network' }[current.kind];
      const graphClass = current.kind === 'proofs' ? ' proof-network-figure' : '';
      const data = JSON.stringify({ [current.kind]: current.data }).replace(/</g, '\\u003c');
      return route.fulfill({ contentType: 'text/html', body: `<!doctype html><meta charset="utf-8"><link rel="stylesheet" href="assets/style.css"><figure class="graph-figure${graphClass}"><div id="${id}" class="figure-container" data-graph="${current.kind}" data-ancestry="true" data-descendants="true"></div><div class="graph-tooltip" hidden></div></figure><script type="application/json" id="graph-data">${data}</script><script src="assets/layout.js"></script><script src="assets/dag.js"></script>` });
    }
    const file = path.join(oldSite, url.pathname);
    if (!fs.existsSync(file) || !fs.statSync(file).isFile()) return route.abort();
    const mime = { '.css': 'text/css', '.js': 'text/javascript', '.woff2': 'font/woff2' }[path.extname(file)];
    return route.fulfill({ body: fs.readFileSync(file), contentType: mime ?? 'application/octet-stream' });
  });
  const page = await context.newPage();
  const errors = [];
  page.on('pageerror', (error) => errors.push(error.message));
  for (const graph of corpus.graphs) {
    current = graph;
    const jsonFile = path.join(out, graph.id + '.json');
    if (fs.existsSync(jsonFile)) { rows.push(JSON.parse(fs.readFileSync(jsonFile, 'utf8'))); continue; }
    errors.length = 0;
    await page.goto('https://baseline.test/fixture.html');
    await page.evaluate(() => document.fonts.ready);
    const rendered = await page.evaluate(() => {
      const svg = document.querySelector('.figure-container svg');
      if (!svg) return { svg: null, nodes: [], paths: [], width: 0, height: 0 };
      const rect = (element) => {
        const b = element.getBBox();
        const m = svg.getCTM().inverse().multiply(element.getCTM());
        const p = new DOMPoint(b.x, b.y).matrixTransform(m);
        return { x: p.x, y: p.y, width: b.width * m.a, height: b.height * m.d };
      };
      const nodes = [...svg.querySelectorAll('.dag-node, .net-node, .net-proof, .net-dock')].map((node) => ({
        id: node.getAttribute('aria-label'), box: rect(node.querySelector('rect, circle')),
        label: node.querySelector('text')?.textContent, ink: rect(node.querySelector('text')),
      }));
      const paths = [...svg.querySelectorAll('.dag-edge, .net-edge')].map((edge) => ({ d: edge.getAttribute('d'), kind: edge.getAttribute('class') }));
      return { svg: svg.outerHTML, nodes, paths, width: svg.viewBox.baseVal.width, height: svg.viewBox.baseVal.height };
    });
    if (rendered.svg) fs.writeFileSync(path.join(out, graph.id + '.svg'), rendered.svg);
    // Equal zoom/viewport; full geometry is in SVG. The PNG is explicitly a
    // viewport capture and is not represented as a fit-to-page comparison.
    await page.screenshot({ path: path.join(out, graph.id + '.png') });
    const { svg, ...geometry } = rendered;
    const row = { id: graph.id, kind: graph.kind, split: graph.split, ...geometry, errors: [...errors] };
    fs.writeFileSync(jsonFile, JSON.stringify(row) + '\n');
    rows.push(row);
    if (rows.length % 50 === 0) console.log(`${rows.length}/${corpus.graphs.length} baseline views captured`);
  }
  fs.writeFileSync(path.join(out, 'manifest.json'), JSON.stringify({ rendererRevision: corpus.rendererRevision, databaseRevision: corpus.databaseRevision, browser: browser.version(), viewport: { width: 1280, height: 900, scale: 1 }, screenshot: 'unscaled viewport; full diagram in SVG', graphs: rows.map(({ id, kind, errors }) => ({ id, kind, errors })) }, null, 2));
  fs.writeFileSync(path.join(out, 'index.html'), `<!doctype html><meta charset="utf-8"><title>Frozen old graph output</title><link rel="stylesheet" href="assets/style.css"><main><h1>Frozen old graph output</h1><p>Equal 1280 × 900 viewport, 100% zoom. SVG links contain the complete drawing. Browser: ${browser.version()}.</p>${rows.map((row) => `<details><summary>${row.kind} ${row.id.slice(0, 12)} (${row.split}), ${row.nodes.length} nodes / ${row.paths.length} edges</summary><a href="${row.id}.svg">Complete SVG</a><img loading="lazy" src="${row.id}.png" width="1280" height="900"></details>`).join('\n')}</main>`);
  console.log(`Captured ${rows.length} views in ${out}`);
} finally { await browser.close(); }
