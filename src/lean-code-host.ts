/** Build tooling only: the public site never imports this Lean LSP client. */
import { spawn, execFile, type ChildProcessWithoutNullStreams } from "node:child_process";
import { promisify } from "node:util";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { identifierComponents, leanHoverTokens, scanLeanSource } from "./sitegen/lean-source.js";
import { leanCodeInputs, parseLeanCode, requireCones, type LeanCodeData, type SourceHover } from "./sitegen/lean-code.js";
import { coneCacheFile, coneDeclarations, coneDigest, dependencyCone, validateConeModule, verifiedConeFile, type ConeModule } from "./sitegen/dependency-cones.js";
import type { SiteModel } from "./sitegen/model.js";

export function hoverType(result: unknown): string | undefined {
  const value = (result as { contents?: { kind?: string; value?: string } } | null)?.contents;
  if (value?.kind !== "markdown" || typeof value.value !== "string") return;
  // Documentation may contain identities and arbitrary Markdown. Publish only
  // Lean's first signature block, as text, never its documentation or links.
  return /^```lean\n([^]*?)\n```(?:\n|$)/.exec(value.value)?.[1]?.trim();
}

const notationHelpers = new Map<string, Promise<void>>();

function prepareNotationHelper(lean: string, root: string, leanPath: string): Promise<void> {
  const key = `${lean}:${root}`;
  let task = notationHelpers.get(key);
  if (!task) {
    task = (async () => {
      const file = path.join(root, "LaxWebsiteNotation.lean");
      fs.copyFileSync(new URL("../scripts/lean-code-notation.lean", import.meta.url), file);
      await promisify(execFile)(lean, ["-o", file.replace(/\.lean$/, ".olean"), file], {
        cwd: root, env: { ...process.env, LEAN_PATH: leanPath }, timeout: 120_000, maxBuffer: 8 * 1024 * 1024,
      });
    })();
    notationHelpers.set(key, task);
  }
  return task;
}

export class LeanHoverClient {
  private process: ChildProcessWithoutNullStreams;
  private buffer = Buffer.alloc(0);
  private sequence = 0;
  private pending = new Map<number, { resolve: (value: any) => void; reject: (error: Error) => void; timer: NodeJS.Timeout }>();
  private errors = new Map<string, string[]>();
  private checkedDocument?: { uri: string; text: string; version: number };
  constructor(private lean: string, private root: string, private leanPath: string) {
    this.process = spawn(lean, ["--server"], { cwd: root, env: { ...process.env, LEAN_PATH: leanPath } });
    let stderr = "";
    this.process.stderr.on("data", data => { stderr = (stderr + data.toString()).slice(-4096); });
    const fail = (error: Error) => {
      for (const pending of this.pending.values()) { clearTimeout(pending.timer); pending.reject(error); }
      this.pending.clear();
    };
    this.process.on("error", fail);
    this.process.on("exit", code => fail(new Error(`Lean server exited (${code}): ${stderr}`)));
    this.process.stdout.on("data", data => {
      this.buffer = Buffer.concat([this.buffer, data]);
      for (;;) {
        const header = this.buffer.indexOf("\r\n\r\n");
        if (header < 0) break;
        const size = Number(/Content-Length: (\d+)/i.exec(this.buffer.subarray(0, header).toString())?.[1]);
        // Declaration metadata can cover thousands of statements in one file.
        if (!Number.isSafeInteger(size) || size > 64 * 1024 * 1024) { fail(new Error("invalid Lean LSP frame")); this.process.kill(); break; }
        if (this.buffer.length < header + 4 + size) break;
        const message = JSON.parse(this.buffer.subarray(header + 4, header + 4 + size).toString());
        this.buffer = this.buffer.subarray(header + 4 + size);
        if (message.method) {
          // Server requests have their own IDs, which may match our requests.
          if (message.id !== undefined) this.send({ id: message.id, result: null });
          if (message.method === "textDocument/publishDiagnostics")
            this.errors.set(message.params.uri, message.params.diagnostics.filter((d: any) => d.severity === 1).map((d: any) => d.message));
        } else {
          const pending = this.pending.get(message.id);
          if (!pending) continue;
          this.pending.delete(message.id); clearTimeout(pending.timer);
          if (message.error) pending.reject(new Error(JSON.stringify(message.error)));
          else pending.resolve(message.result);
        }
      }
    });
  }
  private send(message: object): void {
    const body = JSON.stringify({ jsonrpc: "2.0", ...message });
    this.process.stdin.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  }
  private request(method: string, params: unknown): Promise<any> {
    const id = ++this.sequence;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => { this.pending.delete(id); reject(new Error(`Lean timed out: ${method}`)); this.process.kill(); }, 120_000);
      this.pending.set(id, { resolve, reject, timer }); this.send({ id, method, params });
    });
  }
  async initialize(): Promise<void> {
    await prepareNotationHelper(this.lean, this.root, this.leanPath);
    await this.request("initialize", { processId: process.pid, rootUri: pathToFileURL(this.root).href, capabilities: {} });
    this.send({ method: "initialized", params: {} });
  }
  async hovers(file: string, source: string, onCones?: (data: ConeModule) => void, cachedHovers?: SourceHover[]): Promise<SourceHover[]> {
    const uri = pathToFileURL(file).href;
    const scanned = scanLeanSource(source);
    // Keep module/prelude directives first. Only the server's copy gets the
    // helper import; published source and compiled archive modules stay intact.
    let insertionLine = 0;
    for (const token of scanned.tokens) {
      if (!["module", "prelude"].includes(token.text)) break;
      insertionLine = token.line;
    }
    const lines = source.split("\n");
    lines.splice(insertionLine, 0, "import LaxWebsiteNotation");
    this.send({ method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version: 1, text: lines.join("\n") } } });
    let keepAlive: NodeJS.Timeout | undefined;
    try {
      await this.request("textDocument/waitForDiagnostics", { uri, version: 1 });
      const errors = this.errors.get(uri) ?? [];
      if (errors.length) throw new Error(`${file}: ${errors.join("\n")}`);
      const { sessionId } = await this.request("$/lean/rpc/connect", { uri });
      keepAlive = setInterval(() => this.send({ method: "$/lean/rpc/keepAlive", params: { uri, sessionId } }), 10_000);
      if (onCones) {
        const position = { line: lines.length - 1, character: 0 };
        const raw = await this.request("$/lean/rpc/call", {
          textDocument: { uri }, position, sessionId, method: "LaxWebsiteCones.moduleInfo", params: position,
        });
        const original = source.split("\n"), starts = [0];
        for (const line of original) starts.push(starts.at(-1)! + line.length + 1);
        const offset = (p: { line: number; character: number }) => {
          const line = p.line - (p.line > insertionLine ? 1 : 0);
          if (p.line === insertionLine || !Number.isInteger(line) || line < 0 || line >= original.length ||
              !Number.isInteger(p.character) || p.character < 0 || p.character > original[line]!.length)
            throw new Error("invalid dependency cone source position");
          return starts[line]! + p.character;
        };
        const data: ConeModule = {
          version: 1,
          namespaces: raw.namespaces,
          references: raw.references.map((r: any) => ({ name: r.name, start: offset(r.start), end: offset(r.stop) })),
          commands: raw.commands.map((cmd: any) => ({ start: offset(cmd.start), end: offset(cmd.stop), kind: cmd.kind, uses: cmd.uses })),
          declarations: raw.declarations.map((d: any) => ({ name: d.name, command: d.command, dependencies: d.dependencies,
            ...(d.start && d.stop ? { selection: { start: offset(d.start), end: offset(d.stop) } } : {}) })),
        };
        // Internal names sometimes inherit a zero-width or parent selection.
        for (const declaration of data.declarations) {
          const range = declaration.selection, command = data.commands[declaration.command];
          if (range && (range.start >= range.end || !command || range.start < command.start || range.end > command.end))
            delete declaration.selection;
        }
        validateConeModule(data, source); onCones(data);
      }
      if (cachedHovers) return cachedHovers;
      const currentModule = path.relative(this.root, file).replace(/\.lean$/, "").split(path.sep).join(".");
      const result: SourceHover[] = [];
      const queries = leanHoverTokens(scanned).flatMap(token => {
        const components = token.name ? identifierComponents(token) : [token];
        return components.map(component => ({ token, component, components }));
      });
      for (let i = 0; i < queries.length; i += 16) {
        const batch = await Promise.all(queries.slice(i, i + 16).map(async ({ token, component, components }) => {
          const line = token.line - 1 + (token.line - 1 >= insertionLine ? 1 : 0);
          const position = { line, character: token.column + component.start - token.start };
          if (token.notation) {
            const operator = await this.request("$/lean/rpc/call", {
              textDocument: { uri }, position, sessionId,
              method: "LaxWebsiteNotation.operatorInfo", params: position,
            });
            if (!operator || typeof operator.name !== "string" || !operator.name ||
              typeof operator.type !== "string" || !operator.type || operator.type.length > 32768 ||
              typeof operator.moduleName !== "string" || !Number.isSafeInteger(operator.line) || operator.line < 1) return;
            const definition = { name: operator.name, module: operator.moduleName || currentModule,
              line: operator.line - (!operator.moduleName && operator.line > insertionLine + 1 ? 1 : 0) };
            return { start: token.start, end: token.end, text: `${operator.name} : ${operator.type}`, definition };
          }
          const hover = await this.request("textDocument/hover", { textDocument: { uri }, position });
          const text = hoverType(hover);
          const range = hover?.range;
          const start = token.start + (range?.start.character - token.column);
          const end = token.start + (range?.end.character - token.column);
          // Lean distinguishes a real receiver (`n` in `n.succ`) from a
          // namespace (`Nat.succ`) by returning a narrower hover range.
          return text && text.length <= 32768 && range?.start.line === line && range?.end.line === line &&
            [token, ...components].some(span => span.start === start && span.end === end)
            ? { start, end, text } : undefined;
        }));
        result.push(...batch.filter((entry): entry is SourceHover => entry !== undefined));
      }
      // Qualified namespaces return the same whole-name range at every
      // component. Receivers and their projections return separate ranges.
      const unique: SourceHover[] = [];
      for (const hover of result.sort((a, b) => a.start - b.start || a.end - b.end)) {
        if (hover.start >= (unique.at(-1)?.end ?? 0)) unique.push(hover);
      }
      return unique;
    } finally {
      clearInterval(keepAlive);
      this.send({ method: "textDocument/didClose", params: { textDocument: { uri } } }); this.errors.delete(uri);
    }
  }
  async check(file: string, source: string): Promise<void> {
    const uri = pathToFileURL(file).href;
    const previous = this.checkedDocument;
    if (previous?.uri === uri && previous.text === source) {
      const errors = this.errors.get(uri) ?? [];
      if (errors.length) throw new Error(errors.join("\n"));
      return;
    }
    const version = previous?.uri === uri ? previous.version + 1 : 1;
    this.errors.delete(uri);
    this.checkedDocument = { uri, text: source, version };
    if (previous?.uri === uri) {
      // Keep the unchanged prefix: Lean can reuse imported Mathlib and the
      // common dependencies instead of starting a worker for every export.
      let start = 0, suffix = 0;
      while (start < Math.min(previous.text.length, source.length) && previous.text[start] === source[start]) start++;
      const lowSurrogate = (n: number) => n >= 0xdc00 && n <= 0xdfff;
      if (lowSurrogate(previous.text.charCodeAt(start))) start--;
      while (suffix < Math.min(previous.text.length, source.length) - start &&
        previous.text.at(-1 - suffix) === source.at(-1 - suffix)) suffix++;
      if (lowSurrogate(previous.text.charCodeAt(previous.text.length - suffix))) suffix--;
      const position = (offset: number) => {
        const prefix = previous.text.slice(0, offset), lines = prefix.split("\n");
        return { line: lines.length - 1, character: lines.at(-1)!.length };
      };
      this.send({ method: "textDocument/didChange", params: { textDocument: { uri, version }, contentChanges: [{
        range: { start: position(start), end: position(previous.text.length - suffix) },
        text: source.slice(start, source.length - suffix),
      }] } });
    } else {
      if (previous) this.send({ method: "textDocument/didClose", params: { textDocument: { uri: previous.uri } } });
      this.send({ method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version, text: source } } });
    }
    await this.request("textDocument/waitForDiagnostics", { uri, version });
    const errors = this.errors.get(uri) ?? [];
    if (errors.length) throw new Error(errors.join("\n"));
  }
  async close(): Promise<void> {
    try { await this.request("shutdown", null); this.send({ method: "exit" }); }
    finally { this.process.kill(); }
  }
}

export async function prepareLeanEnvironment(model: SiteModel, options: {
  version: string; lean: string; packages: string; work: string; cache: string; jobs?: number; log?: (line: string) => void;
}): Promise<void> {
  const ids = [...model.conceptHome].filter(([, c]) => c.output.manifest.leanVersion === options.version).map(([id]) => id);
  const inputs = new Map(ids.map(id => [id, leanCodeInputs(model, id)]));
  const pending = ids.filter(id => {
    const { digest } = inputs.get(id)!;
    try {
      const source = model.conceptHome.get(id)!.concept.sourceText;
      const data = parseLeanCode(fs.readFileSync(path.join(options.cache, `${digest}.json`), "utf8"), digest, source);
      requireCones(data, source, options.cache);
      return false;
    } catch { return true; }
  });
  if (!pending.length) return;
  const ordered = [...new Set(pending.flatMap(id => inputs.get(id)!.modules))];
  const neededObjects = new Set(ordered.flatMap(id => model.conceptHome.get(id)!.concept.imports));
  fs.mkdirSync(options.work, { recursive: true }); fs.mkdirSync(options.cache, { recursive: true });
  const libraries = fs.readdirSync(options.packages).sort().map(p => path.join(options.packages, p, ".lake/build/lib/lean"));
  const leanPath = [options.work, ...libraries].join(path.delimiter);
  const fileOf = (id: string) => {
    if (!/^[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*$/.test(id)) throw new Error(`unsupported module path ${id}`);
    return path.join(options.work, `${id.replaceAll(".", "/")}.lean`);
  };
  // Write the actual modules, preserving their contexts and import boundaries.
  for (const id of ordered) {
    const file = fileOf(id); fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, model.conceptHome.get(id)!.concept.sourceText);
  }
  const clients = Array.from({ length: options.jobs ?? 2 }, () => new LeanHoverClient(options.lean, options.work, leanPath));
  await Promise.all(clients.map(client => client.initialize()));
  const available = [...clients], waiting: ((client: LeanHoverClient) => void)[] = [];
  const acquire = () => available.length ? Promise.resolve(available.pop()!) : new Promise<LeanHoverClient>(resolve => waiting.push(resolve));
  const release = (client: LeanHoverClient) => { const next = waiting.shift(); if (next) next(client); else available.push(client); };
  const tasks = new Map<string, Promise<void>>();
  let done = 0;
  try {
    for (const id of ordered) {
      const dependencies = model.conceptHome.get(id)!.concept.imports.map(name => tasks.get(name)!);
      tasks.set(id, Promise.all(dependencies).then(async () => {
      const client = await acquire();
      try {
      const source = model.conceptHome.get(id)!.concept.sourceText, file = fileOf(id);
      // Only imported modules need an object file. The language server
      // elaborates leaf modules itself, so don't compile those twice.
      if (neededObjects.has(id)) await promisify(execFile)(options.lean, ["-o", file.replace(/\.lean$/, ".olean"), file], {
        cwd: options.work, env: { ...process.env, LEAN_PATH: leanPath }, timeout: 120_000, maxBuffer: 8 * 1024 * 1024,
      });
      const input = inputs.get(id);
      if (!input) return;
      const cacheFile = path.join(options.cache, `${input.digest}.json`);
      let cached: LeanCodeData | undefined;
      try { cached = parseLeanCode(fs.readFileSync(cacheFile, "utf8"), input.digest, source); } catch { /* Rebuild missing/corrupt cache. */ }
      let cones = cached?.cones;
      if (cones?.references) { model.leanCode.set(id, cached!); done++; return; }
      const hovers = await client.hovers(file, source, data => { cones = data; }, cached?.hovers);
      if (cones && cached?.cones?.exports) cones.exports = cached.cones.exports;
      const data: LeanCodeData = { version: 1, projectionHovers: 1, numericHovers: 1, digest: input.digest, hovers, cones };
      fs.writeFileSync(`${cacheFile}.tmp`, JSON.stringify(data) + "\n"); fs.renameSync(`${cacheFile}.tmp`, cacheFile);
      model.leanCode.set(id, data);
      options.log?.(`${options.version}: ${++done}/${ordered.length} ${id}: ${data.hovers.length} type hovers`);
      } finally { release(client); }
      }));
    }
    const results = await Promise.allSettled(tasks.values());
    const failed = results.find(result => result.status === "rejected");
    if (failed?.status === "rejected") throw failed.reason;
    fs.mkdirSync(path.join(options.cache, "cones"), { recursive: true });
    const validations = new Map<string, Promise<string>>();
    const exports = await Promise.allSettled(pending.map(async id => {
      const data = model.leanCode.get(id)!, source = model.conceptHome.get(id)!.concept.sourceText;
      const entries: NonNullable<ConeModule["exports"]> = [];
      const declarations = coneDeclarations(data.cones!, source);
      for (const declaration of declarations) {
        let text = dependencyCone(model, id, declaration.name), digest = coneDigest(text);
        let task = validations.get(digest);
        if (!task) {
          task = (async () => {
            try { verifiedConeFile(options.cache, digest); return digest; } catch { /* Validate before publishing. */ }
            const client = await acquire();
            try {
              const fileToCheck = path.join(options.work, `LaxWebsiteCone${clients.indexOf(client)}.lean`);
              try { await client.check(fileToCheck, text); }
              catch (error) {
                const qualified = dependencyCone(model, id, declaration.name, true);
                if (qualified === text) throw error;
                await client.check(fileToCheck, qualified);
                text = qualified; digest = coneDigest(text);
              }
              const file = coneCacheFile(options.cache, digest);
              fs.writeFileSync(`${file}.tmp`, text); fs.renameSync(`${file}.tmp`, file);
              return digest;
            } catch (error) {
              throw new Error(`${declaration.name}: dependency cone does not elaborate: ${error instanceof Error ? error.message : error}`);
            } finally { release(client); }
          })();
          validations.set(digest, task);
        }
        entries.push({ name: declaration.name, digest: await task });
        if (entries.length % 100 === 0)
          options.log?.(`${options.version}: ${id}: ${entries.length}/${declarations.length} checked dependency cones`);
      }
      data.cones!.exports = entries;
      const cacheFile = path.join(options.cache, `${data.digest}.json`);
      fs.writeFileSync(`${cacheFile}.tmp`, JSON.stringify(data) + "\n"); fs.renameSync(`${cacheFile}.tmp`, cacheFile);
      options.log?.(`${options.version}: ${id}: ${entries.length} checked dependency cones`);
    }));
    const exportFailure = exports.find(result => result.status === "rejected");
    if (exportFailure?.status === "rejected") throw exportFailure.reason;
  } finally { await Promise.all(clients.map(client => client.close())); }
}
