/** A small lexical inventory, not a Lean parser or name resolver. Keep source
 * offsets in UTF-16, like JavaScript and Shiki. Unknown syntax stays plain. */
export interface SourceRange { start: number; end: number }
export interface LeanToken extends SourceRange {
  text: string;
  line: number;
  column: number;
  /** Start of standalone comments immediately before this token. */
  leadingCommentLine?: number;
  /** Components keep `A.«B.C»` distinct from `A.B.C`. */
  name?: string[];
}
export interface LeanSource {
  tokens: LeanToken[];
  comments: SourceRange[];
}

// Lean's Init/Meta/Defs.lean: isIdFirst/isIdRest. In particular !, ?, primes
// and subscripts belong to the identifier; never link a truncated prefix.
const LETTER = "a-zA-Z_\\u00c0-\\u00d6\\u00d8-\\u00f6\\u00f8-\\u017f\\u0391-\\u039f\\u03a1-\\u03a2\\u03a4-\\u03a9\\u03b1-\\u03ba\\u03bc-\\u03fb\\u1f00-\\u1ffe\\u2100-\\u214f\\u{1d49c}-\\u{1d59f}";
const PART = `(?:[${LETTER}][${LETTER}0-9'!?\\u2080-\\u2089\\u2090-\\u209c\\u1d62-\\u1d6a\\u2c7c]*|«[^»\\r\\n]*»)`;
const NAME = new RegExp(`${PART}(?:\\.${PART})*`, "uy");
const COMPONENT = new RegExp(PART, "gu");
const RAW_STRING = /r(#+)?"/y;

export function nameParts(text: string): string[] {
  return [...text.matchAll(COMPONENT)].map(([part]) => part.startsWith("«") ? part.slice(1, -1) : part);
}

export function nameKey(parts: readonly string[]): string { return JSON.stringify(parts); }

/** Comments nest. Strings (including raw strings), characters and syntax
 * quotations are data: no declarations or clickable references inside them. */
export function scanLeanSource(source: string): LeanSource {
  const tokens: LeanToken[] = [];
  const comments: SourceRange[] = [];
  let index = 0;
  let line = 1;
  let lineStart = 0;
  let quotedDepth = 0;
  let lastCodeLine = 0;
  let leadingCommentLine: number | undefined;
  const code = () => { lastCodeLine = line; leadingCommentLine = undefined; };
  const token = (value: LeanToken) => {
    if (!quotedDepth) tokens.push({ ...value, leadingCommentLine });
  };
  const advance = (end: number) => {
    while (index < end) if (source[index++] === "\n") { line++; lineStart = index; }
  };
  while (index < source.length) {
    const start = index;
    if (/\s/u.test(source[index]!)) { advance(index + 1); continue; }
    if (source.startsWith("--", index)) {
      if (!quotedDepth && line > lastCodeLine) leadingCommentLine ??= line;
      const end = source.indexOf("\n", index + 2);
      advance(end < 0 ? source.length : end);
      if (!quotedDepth) comments.push({ start, end: index });
      continue;
    }
    if (source.startsWith("/-", index)) {
      if (source.startsWith("/-!", index)) leadingCommentLine = undefined;
      else if (!quotedDepth && line > lastCodeLine) leadingCommentLine ??= line;
      let depth = 1;
      advance(index + 2);
      while (index < source.length && depth) {
        if (source.startsWith("/-", index)) { depth++; advance(index + 2); }
        else if (source.startsWith("-/", index)) { depth--; advance(index + 2); }
        else advance(index + 1);
      }
      if (!quotedDepth) comments.push({ start, end: index });
      continue;
    }
    // Lean raw strings use r###"..."### (any number of hashes).
    RAW_STRING.lastIndex = index;
    const raw = RAW_STRING.exec(source);
    if (raw) {
      const delimiter = `"${raw[1] ?? ""}`;
      const end = source.indexOf(delimiter, index + raw[0].length);
      advance(end < 0 ? source.length : end + delimiter.length);
      code();
      continue;
    }
    if (source[index] === '"' || source[index] === "'") {
      const delimiter = source[index]!;
      advance(index + 1);
      while (index < source.length) {
        if (source[index] === "\\") advance(Math.min(index + 2, source.length));
        else if (source[index] === delimiter) { advance(index + 1); break; }
        else advance(index + 1);
      }
      code();
      continue;
    }
    if (source[index] === "`") {
      advance(index + 1);
      if (source[index] === "`") advance(index + 1);
      if (source[index] === "(") { quotedDepth++; advance(index + 1); }
      else {
        NAME.lastIndex = index;
        const quoted = NAME.exec(source);
        if (quoted) advance(index + quoted[0].length);
      }
      code();
      continue;
    }
    NAME.lastIndex = index;
    const identifier = NAME.exec(source)?.[0];
    if (identifier) {
      token({ start, end: index + identifier.length, text: identifier, line, column: start - lineStart, name: nameParts(identifier) });
      advance(index + identifier.length);
      code();
      continue;
    }
    const symbol = String.fromCodePoint(source.codePointAt(index)!);
    if (quotedDepth) {
      if (symbol === "(") quotedDepth++;
      if (symbol === ")") quotedDepth--;
    } else token({ start, end: index + symbol.length, text: symbol, line, column: start - lineStart });
    advance(index + symbol.length);
    code();
  }
  return { tokens, comments };
}

export interface LeanDeclaration {
  token: LeanToken;
  /** First preceding comment, or the declaration's attributes/modifiers. */
  startLine: number;
  name: string[];
  private: boolean;
}

export interface LeanNamespaceReference {
  token: LeanToken;
  namespace: readonly string[];
  kind: "open" | "namespace" | "end";
}

const DECLARATION = new Set(["def", "abbrev", "structure", "class", "inductive", "theorem", "lemma", "axiom", "opaque", "constant"]);
const MODIFIER = new Set(["private", "protected", "noncomputable", "unsafe", "partial", "nonrec", "public"]);

/** Inventory ordinary command declarations and namespace/section nesting.
 * Optionally visit identifier uses with their current namespace, sharing the
 * same command walk. Declaration names and scope labels are not references.
 * Does not invent names for fields, macros, `export`, or `where` helpers. */
export function leanDeclarations(
  { tokens }: LeanSource,
  reference?: (token: LeanToken, namespace: readonly string[]) => void,
  namespaceReference?: (reference: LeanNamespaceReference) => void,
): LeanDeclaration[] {
  const result: LeanDeclaration[] = [];
  const scopes: { namespace: string[]; kind: "namespace" | "section" }[] = [];
  let namespace: string[] = [];
  let bodyNamespace: string[] | undefined;
  let commandColumn = 0;
  let depth = 0;
  let prefix = false;
  let startLine = 1;
  let isPrivate = false;
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i]!;
    const text = token.text;
    const first = i === 0 || tokens[i - 1]!.line < token.line;
    const commandStart = first && !depth && (bodyNamespace === undefined || token.column <= commandColumn);
    if (commandStart) bodyNamespace = undefined;
    const visit = () => {
      // `.field` and `(term).field` need type information, not namespace lookup.
      if (token.name && tokens[i - 1]?.text !== ".") reference?.(token, bodyNamespace ?? namespace);
    };
    if (text === "open" && namespaceReference) {
      // Namespace operands precede any selective opening/hiding/renaming.
      // Stop at `in` and at a new command's indentation; selected declaration
      // names keep their compiler-provided links, never namespace guesses.
      for (let j = i + 1; j < tokens.length; j++) {
        const next = tokens[j]!;
        if (next.line > token.line && next.column <= commandColumn) break;
        if (j === i + 1 && next.text === "scoped") continue;
        if (next.text === "(") {
          let selectionDepth = 1;
          while (++j < tokens.length && selectionDepth) {
            if (tokens[j]!.text === "(") selectionDepth++;
            if (tokens[j]!.text === ")") selectionDepth--;
          }
          j--;
          continue;
        }
        if (!next.name || ["in", "hiding", "renaming"].includes(next.text)) break;
        namespaceReference({ token: next, namespace: bodyNamespace ?? namespace, kind: "open" });
      }
    }
    if (["(", "[", "{", "⦃"].includes(text)) { depth++; continue; }
    if ([")", "]", "}", "⦄"].includes(text)) { depth = Math.max(0, depth - 1); continue; }
    if (depth) { visit(); continue; }
    if (commandStart && !prefix) {
      prefix = true;
      commandColumn = token.column;
      startLine = token.leadingCommentLine ?? token.line;
    }
    if (!prefix) { visit(); continue; }
    if (text === "@" && tokens[i + 1]?.text === "[") continue;
    if (MODIFIER.has(text)) { if (text === "private") isPrivate = true; continue; }
    if (text === "namespace" || text === "section") {
      scopes.push({ namespace, kind: text });
      if (text === "namespace" && tokens[i + 1]?.name) {
        const parts = tokens[i + 1]!.name!;
        namespace = parts[0] === "_root_" ? parts.slice(1) : [...namespace, ...parts];
        namespaceReference?.({ token: tokens[i + 1]!, namespace, kind: "namespace" });
      }
      if (tokens[i + 1]?.name && tokens[i + 1]!.line === token.line) i++;
    } else if (text === "end") {
      const scope = scopes.pop();
      if (scope?.kind === "namespace" && tokens[i + 1]?.name && tokens[i + 1]!.line === token.line)
        namespaceReference?.({ token: tokens[i + 1]!, namespace, kind: "end" });
      namespace = scope?.namespace ?? [];
      if (tokens[i + 1]?.name && tokens[i + 1]!.line === token.line) i++;
    } else if (DECLARATION.has(text) && tokens[i + 1]?.name) {
      const declared = tokens[i + 1]!;
      const parts = declared.name!;
      const name = parts[0] === "_root_" ? parts.slice(1) : [...namespace, ...parts];
      result.push({ token: declared, startLine, name, private: isPrivate });
      // `def A.f` elaborates its signature/body in namespace A, even without
      // an explicit `namespace A` command. A new command ends that context.
      bodyNamespace = name.slice(0, -1);
      i++;
    } else if (text === "#" && tokens[i + 1]?.name) {
      i++; // The name in `#check`, `#eval`, etc. is a command, not a term.
    }
    prefix = false;
    isPrivate = false;
  }
  return result;
}
