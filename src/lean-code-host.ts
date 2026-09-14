/** Build tooling only: the public site never imports this Lean LSP client. */
import { spawn, execFile, type ChildProcessWithoutNullStreams } from "node:child_process";
import { promisify } from "node:util";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { scanLeanSource } from "./sitegen/lean-source.js";
import { leanCodeInputs, parseLeanCode, type LeanCodeData, type SourceHover } from "./sitegen/lean-code.js";
import type { SiteModel } from "./sitegen/model.js";

export function hoverType(result: unknown): string | undefined {
  const value = (result as { contents?: { kind?: string; value?: string } } | null)?.contents;
  if (value?.kind !== "markdown" || typeof value.value !== "string") return;
  // Documentation may contain identities and arbitrary Markdown. Publish only
  // Lean's first signature block, as text, never its documentation or links.
  return /^```lean\n([^]*?)\n```(?:\n|$)/.exec(value.value)?.[1]?.trim();
}

export class LeanHoverClient {
  private process: ChildProcessWithoutNullStreams;
  private buffer = Buffer.alloc(0);
  private sequence = 0;
  private pending = new Map<number, { resolve: (value: any) => void; reject: (error: Error) => void; timer: NodeJS.Timeout }>();
  private errors = new Map<string, string[]>();
  constructor(lean: string, private root: string, leanPath: string) {
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
        if (!Number.isSafeInteger(size) || size > 16 * 1024 * 1024) { fail(new Error("invalid Lean LSP frame")); this.process.kill(); break; }
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
    await this.request("initialize", { processId: process.pid, rootUri: pathToFileURL(this.root).href, capabilities: {} });
    this.send({ method: "initialized", params: {} });
  }
  async hovers(file: string, source: string): Promise<SourceHover[]> {
    const uri = pathToFileURL(file).href;
    this.send({ method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version: 1, text: source } } });
    try {
      await this.request("textDocument/waitForDiagnostics", { uri, version: 1 });
      const errors = this.errors.get(uri) ?? [];
      if (errors.length) throw new Error(`${file}: ${errors.join("\n")}`);
      const result: SourceHover[] = [];
      const tokens = scanLeanSource(source).tokens.filter(t => t.name);
      for (let i = 0; i < tokens.length; i += 16) {
        const batch = await Promise.all(tokens.slice(i, i + 16).map(async token => {
          const hover = await this.request("textDocument/hover", { textDocument: { uri }, position: { line: token.line - 1, character: token.column } });
          const text = hoverType(hover);
          const range = hover?.range;
          return text && text.length <= 32768 && range?.start.line === token.line - 1 && range?.end.line === token.line - 1 &&
            range.start.character === token.column && range.end.character === token.column + token.end - token.start
            ? { start: token.start, end: token.end, text } : undefined;
        }));
        result.push(...batch.filter((entry): entry is SourceHover => entry !== undefined));
      }
      return result;
    } finally {
      this.send({ method: "textDocument/didClose", params: { textDocument: { uri } } }); this.errors.delete(uri);
    }
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
  const ordered = [...new Set([...inputs.values()].flatMap(input => input.modules))];
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
      // Compile dependencies before requesting editor information for users.
      await promisify(execFile)(options.lean, ["-o", file.replace(/\.lean$/, ".olean"), file], {
        cwd: options.work, env: { ...process.env, LEAN_PATH: leanPath }, timeout: 120_000, maxBuffer: 8 * 1024 * 1024,
      });
      const input = inputs.get(id);
      if (!input) return;
      const cacheFile = path.join(options.cache, `${input.digest}.json`);
      try { parseLeanCode(fs.readFileSync(cacheFile, "utf8"), input.digest, source); done++; return; } catch { /* Rebuild missing/corrupt cache. */ }
      const data: LeanCodeData = { version: 1, digest: input.digest, hovers: await client.hovers(file, source) };
      fs.writeFileSync(`${cacheFile}.tmp`, JSON.stringify(data) + "\n"); fs.renameSync(`${cacheFile}.tmp`, cacheFile);
      options.log?.(`${options.version}: ${++done}/${ordered.length} ${id}: ${data.hovers.length} type hovers`);
      } finally { release(client); }
      }));
    }
    const results = await Promise.allSettled(tasks.values());
    const failed = results.find(result => result.status === "rejected");
    if (failed?.status === "rejected") throw failed.reason;
  } finally { await Promise.all(clients.map(client => client.close())); }
}
