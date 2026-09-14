#!/usr/bin/env node
// Run after npm run build. Host-only tooling; no part ships to visitors.
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {execFileSync} from 'node:child_process';
import {loadSubmissions} from '../dist/database.js';
import {SiteModel} from '../dist/sitegen/model.js';
import {leanCodeInputs, parseLeanCode} from '../dist/sitegen/lean-code.js';
import {prepareLeanEnvironment} from '../dist/lean-code-host.js';
import {landingLeanModel} from '../dist/sitegen/pages/index.js';

const option = (name, fallback) => {
  const index = process.argv.indexOf(name);
  if (index < 0) return fallback;
  if (!process.argv[index + 1] || process.argv[index + 1].startsWith('--')) throw new Error(`${name} requires a value`);
  return process.argv[index + 1];
};
const cache = path.resolve(option('--cache', 'data/lean-code'));
const jobs = Number(option('--jobs', '2'));
if (!Number.isInteger(jobs) || jobs < 1 || jobs > 4) throw new Error('--jobs must be between 1 and 4');
const model = new SiteModel([...loadSubmissions(option('--database', 'data/lax-db')), ...landingLeanModel().submissions]);
const environments = new Map();
for (const {output} of model.conceptHome.values()) {
  const {leanVersion, mathlibVersion} = output.manifest;
  if (!/^v\d+\.\d+\.\d+(?:-rc\d+)?$/.test(leanVersion) || !/^[a-f0-9]{40}$/.test(mathlibVersion)) throw new Error('invalid Lean/Mathlib environment');
  if (environments.has(leanVersion) && environments.get(leanVersion) !== mathlibVersion) throw new Error('conflicting Mathlib pins');
  environments.set(leanVersion, mathlibVersion);
}
const run = (cmd, args, cwd, env) => execFileSync(cmd, args, {cwd, env: {...process.env, ...env}, stdio: 'inherit', timeout: 20 * 60_000});
for (const [version, revision] of [...environments].sort()) {
  if (option('--version', version) !== version) continue;
  const ids = [...model.conceptHome].filter(([, c]) => c.output.manifest.leanVersion === version).map(([id]) => id);
  const missing = ids.filter(id => {
    const {digest} = leanCodeInputs(model, id);
    try { parseLeanCode(fs.readFileSync(path.join(cache, `${digest}.json`), 'utf8'), digest, model.conceptHome.get(id).concept.sourceText); return false; }
    catch { return true; }
  });
  if (!missing.length) { console.log(`${version}: all ${ids.length} modules cached`); continue; }
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'lax-lean-code-'));
  const toolchain = `leanprover/lean4:${version}`;
  const localToolchain = path.join(os.homedir(), '.elan/toolchains', `leanprover--lean4---${version}`);
  const warm = path.join(os.homedir(), '.lax/warm', `${version}-${revision.slice(0, 12)}`);
  let installed = false;
  try {
    if (!fs.existsSync(path.join(localToolchain, 'bin/lean'))) { run('elan', ['toolchain', 'install', toolchain]); installed = true; }
    const lean = path.join(localToolchain, 'bin/lean');
    let packages;
    if (fs.existsSync(path.join(warm, '.lake/packages/mathlib'))) {
      const actual = execFileSync('git', ['-C', path.join(warm, '.lake/packages/mathlib'), 'rev-parse', 'HEAD'], {encoding: 'utf8'}).trim();
      if (actual !== revision) throw new Error(`warm Mathlib pin mismatch for ${version}`);
      packages = path.join(warm, '.lake/packages');
    } else {
      const mathlib = path.join(work, '.lake/packages/mathlib');
      fs.mkdirSync(path.dirname(mathlib), {recursive: true});
      run('git', ['init', mathlib]);
      run('git', ['-C', mathlib, 'fetch', '--depth', '1', 'https://github.com/leanprover-community/mathlib4.git', revision]);
      run('git', ['-C', mathlib, 'checkout', '--detach', 'FETCH_HEAD']);
      const modules = [...new Set(ids.flatMap(id => model.conceptHome.get(id).concept.mathlibImports ?? []))].sort();
      const leanEnvironment = {ELAN_TOOLCHAIN: toolchain, PATH: `${localToolchain}/bin:${process.env.PATH}`};
      run(path.join(localToolchain, 'bin/lake'), ['exe', 'cache', 'get', ...modules], mathlib, leanEnvironment);
      // Mathlib's own dependencies live inside its checkout.
      packages = path.join(work, 'libraries'); fs.mkdirSync(packages);
      fs.symlinkSync(mathlib, path.join(packages, 'mathlib'));
      for (const name of fs.readdirSync(path.join(mathlib, '.lake/packages')))
        fs.symlinkSync(path.join(mathlib, '.lake/packages', name), path.join(packages, name));
    }
    await prepareLeanEnvironment(model, {version, lean, packages, work: path.join(work, 'source'), cache, jobs, log: console.log});
  } finally {
    fs.rmSync(work, {recursive: true, force: true});
    // CI processes environments sequentially to avoid retaining several full
    // Mathlib/toolchain trees. Never remove a user's pre-existing toolchain.
    if (installed && process.env.CI) run('elan', ['toolchain', 'uninstall', toolchain]);
  }
}
