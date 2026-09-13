// Portable development report presentation, using the actual site stylesheet.
// No JavaScript, layout engine, or unrelated PDF assets are copied.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { digest } from './graph-inventory.mjs';

export function copyGraphReportAssets(out) {
  const source = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../assets/site'), target = path.join(out, 'assets');
  const css = fs.readFileSync(path.join(source, 'style.css'), 'utf8');
  const files = new Set(['style.css', 'GUST-FONT-LICENSE.txt', 'DEJAVU-FONT-LICENSE.txt']);
  for (const match of css.matchAll(/url\(\s*['"]?([^'"\s)]+)['"]?\s*\)/g)) {
    const relative = match[1];
    if (/^(?:data:|#)/.test(relative)) continue;
    if (/^(?:[a-z]+:|\/)/i.test(relative) || path.resolve(source, relative).startsWith(source + path.sep) === false) throw new Error(`Nonlocal stylesheet asset ${relative}`);
    files.add(relative);
  }
  const manifest = [];
  for (const file of [...files].sort()) {
    const bytes = fs.readFileSync(path.join(source, file)), destination = path.join(target, file);
    fs.mkdirSync(path.dirname(destination), { recursive: true }); fs.writeFileSync(destination, bytes);
    manifest.push({ file: `assets/${file}`, sha256: createHash('sha256').update(bytes).digest('hex'), bytes: bytes.length });
  }
  // Container rules only; labels and glyph styling remain exactly site CSS.
  const reportCss = '.graph-report{overflow:auto}.graph-report .graph-figure{margin:0;width:max-content;min-width:100%;max-width:none}.graph-report .figure-container{height:auto;overflow:visible}.graph-report .prepared-graph{max-width:none;margin:0}\n';
  fs.writeFileSync(path.join(target, 'report.css'), reportCss);
  manifest.push({ file: 'assets/report.css', sha256: digest(reportCss), bytes: Buffer.byteLength(reportCss) });
  return manifest;
}

export function graphReportPage(svg, title, assetPrefix = '../assets/') {
  const escape = (s) => String(s).replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('"', '&quot;');
  return `<!doctype html><meta charset="utf-8"><title>${escape(title)}</title><link rel="stylesheet" href="${assetPrefix}style.css"><link rel="stylesheet" href="${assetPrefix}report.css"><body class="graph-report"><figure class="graph-figure"><div class="figure-container">${svg}</div></figure></body>`;
}
