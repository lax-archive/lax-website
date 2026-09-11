import type { SourceRange } from "./sitegen/lean-source.js";

export interface LeanLocation extends SourceRange { line: number }
export interface LeanConstantReference {
  module: string;
  name: string;
  definition?: LeanLocation;
  usages: LeanLocation[];
}
export interface LeanReferences {
  module: string;
  constants: LeanConstantReference[];
  declarations: Map<string, { range: LeanLocation; selection: LeanLocation }>;
}

// Version 5 is written by Lean.Server.Ilean. Its positions are zero-based
// LSP (UTF-16), not UTF-8 byte offsets. No Lean code is loaded or executed.
export const MAX_REFERENCE_BYTES = 8 * 1024 * 1024;

function object(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

export function parseLeanReferences(json: string, module: string, source: string): LeanReferences {
  const fail = (reason: string): never => { throw new Error(`${module}: invalid Lean references (${reason})`); };
  if (Buffer.byteLength(json) > MAX_REFERENCE_BYTES) fail("size limit");
  const value: unknown = JSON.parse(json);
  if (!object(value) || value.version !== 5 || value.module !== module ||
    !object(value.references) || !object(value.decls)) return fail("unsupported version, module or schema");
  const lines = source.split("\n");
  const starts: number[] = [];
  let offset = 0;
  for (const line of lines) { starts.push(offset); offset += line.length + 1; }
  const position = (line: unknown, column: unknown): number => {
    if (typeof line !== "number" || !Number.isSafeInteger(line) || line < 0 || line >= lines.length ||
      typeof column !== "number" || !Number.isSafeInteger(column) || column < 0 || column > lines[line]!.length)
      return fail("position outside source");
    const absolute = starts[line]! + column;
    if (absolute > 0 && /[\uD800-\uDBFF]/u.test(source[absolute - 1]!) && /[\uDC00-\uDFFF]/u.test(source[absolute] ?? ""))
      fail("position splits a Unicode character");
    return absolute;
  };
  const range = (tuple: unknown): LeanLocation => {
    if (!Array.isArray(tuple) || tuple.length < 4 || tuple.length > 5) return fail("range tuple");
    const start = position(tuple[0], tuple[1]);
    const end = position(tuple[2], tuple[3]);
    if (end < start) fail("backwards range");
    return { start, end, line: (tuple[0] as number) + 1 };
  };
  const constants: LeanConstantReference[] = [];
  for (const [key, entry] of Object.entries(value.references)) {
    const ident: unknown = JSON.parse(key);
    if (!object(ident)) fail("identifier");
    // Locals (fvars), options and documentation references have no archive
    // declaration target. Only compiler-resolved constants are navigation.
    if (!object(ident) || !Object.hasOwn(ident, "c")) continue;
    if (!object(ident.c) || typeof ident.c.m !== "string" || typeof ident.c.n !== "string" ||
      !ident.c.m || !ident.c.n || !object(entry) || !Array.isArray(entry.usages)) return fail("constant schema");
    const definition = entry.definition == null ? undefined : range(entry.definition);
    if (definition && ident.c.m !== module) fail("foreign definition");
    constants.push({ module: ident.c.m, name: ident.c.n, definition, usages: entry.usages.map(range) });
  }
  const declarations: LeanReferences["declarations"] = new Map();
  for (const [name, tuple] of Object.entries(value.decls)) {
    if (!Array.isArray(tuple) || tuple.length !== 8) return fail("declaration tuple");
    const extent = range(tuple.slice(0, 4));
    const selection = range(tuple.slice(4));
    if (selection.start < extent.start || selection.end > extent.end) fail("declaration selection");
    declarations.set(name, { range: extent, selection });
  }
  return { module, constants, declarations };
}
