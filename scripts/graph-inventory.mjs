// Development-only: freeze the existing, permission-filtered graph payloads.
// Run against a site built at the recorded renderer/database revisions.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';

export const canonical = (value) => JSON.stringify(sortKeys(value));
function sortKeys(value) {
  if (Array.isArray(value)) return value.map(sortKeys);
  if (value && typeof value === 'object') return Object.fromEntries(Object.keys(value).sort().map((key) => [key, sortKeys(value[key])]));
  return value;
}
export const digest = (value) => crypto.createHash('sha256').update(typeof value === 'string' ? value : canonical(value)).digest('hex');

function htmlFiles(root, prefix = '') {
  return fs.readdirSync(path.join(root, prefix), { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : 1).flatMap((entry) => {
    const relative = path.posix.join(prefix, entry.name);
    return entry.isDirectory() ? htmlFiles(root, relative) : entry.name.endsWith('.html') ? [relative] : [];
  });
}

export function inventory(site, rendererRevision, databaseRevision) {
  const unique = new Map();
  const pages = [];
  for (const file of htmlFiles(site)) {
    const html = fs.readFileSync(path.join(site, file), 'utf8');
    const raw = /<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/.exec(html);
    if (!raw) continue;
    const payloads = JSON.parse(raw[1]);
    for (const kind of Object.keys(payloads).sort()) {
      const data = payloads[kind];
      if (!data || !(data.nodes?.length || data.statements?.length || data.proofs?.length)) continue;
      const viewStates = kind === 'concepts' ? ['00', '01', '10', '11'] : ['default'];
      for (const state of viewStates) {
        const view = kind === 'concepts' ? (() => {
          const nodes = data.nodes.filter((node) => node.dir === 'core' || (node.dir === 'up' ? state[0] === '1' : state[1] === '1'));
          const ids = new Set(nodes.map((node) => node.id));
          return { ...data, nodes, edges: data.edges.filter((edge) => ids.has(edge.from) && ids.has(edge.to)) };
        })() : data;
        const id = digest({ kind, view });
        if (!unique.has(id)) unique.set(id, { id, kind, state, data: view, occurrences: [] });
        unique.get(id).occurrences.push({ file, state });
        pages.push({ file, kind, state, id });
      }
    }
  }
  // Split by underlying topology/labels, never by page occurrence. Split is
  // fixed before algorithm selection. Small and large buckets occur in both.
  const graphs = [...unique.values()].sort((a, b) => a.id < b.id ? -1 : 1);
  const strata = new Map();
  for (const graph of graphs) {
    const n = graph.data.nodes?.length ?? graph.data.statements.length + graph.data.proofs.length;
    const grouped = graph.data.statements?.some((node) => node.count > 1) ?? false;
    const key = `${graph.kind}:${n <= 8 ? 'small' : n <= 32 ? 'medium' : 'large'}:${grouped ? 'docks' : 'flat'}`;
    graph.splitGroup = digest({ kind: graph.kind,
      nodes: (graph.data.nodes ?? graph.data.statements).map((node) => [node.id, node.title, node.concept, node.index]).sort(),
      edges: graph.data.edges?.map((edge) => [edge.from, edge.to, edge.kind]).sort(),
      proofs: graph.data.proofs?.map((proof) => [proof.id, [...proof.assumptions].sort(), proof.conclusion]).sort(),
    });
    if (!strata.has(key)) strata.set(key, new Map());
    const groups = strata.get(key);
    if (!groups.has(graph.splitGroup)) groups.set(graph.splitGroup, []);
    groups.get(graph.splitGroup).push(graph);
  }
  for (const [stratum, groups] of strata) [...groups.keys()].sort().forEach((groupId, i) => {
    for (const graph of groups.get(groupId)) {
      graph.stratum = stratum;
      graph.split = i % 3 === 1 ? 'held-out' : 'tuning';
    }
  });
  return { schemaVersion: 1, rendererRevision, databaseRevision, source: 'public archive; rendered presentation payloads only', splitPolicy: 'group equal labeled topology, ignoring decoration/URLs; sha256 group order within kind/size/dock strata; every third group held out (offset 1)', pages, graphs };
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const [site, out, renderer, database] = process.argv.slice(2);
  if (!site || !out || !/^[a-f0-9]{40}$/.test(renderer ?? '') || !/^[a-f0-9]{40}$/.test(database ?? ''))
    throw new Error('usage: node scripts/graph-inventory.mjs SITE OUT RENDERER_SHA DATABASE_SHA');
  const result = inventory(site, renderer, database);
  fs.mkdirSync(path.dirname(out), { recursive: true });
  fs.writeFileSync(out, canonical(result) + '\n');
  console.log(JSON.stringify({ graphs: result.graphs.length, views: result.pages.length, kinds: [...new Set(result.graphs.map((g) => g.kind))], bytes: fs.statSync(out).size }));
}
