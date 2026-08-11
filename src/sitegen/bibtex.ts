// A small, tolerant BibTeX renderer: submission manifests carry raw BibTeX
// entries, and the References section shows them compiled — authors, italic
// title, venue, year, links — the way a paper's bibliography reads, not as
// source code. Anything the parser cannot make sense of falls back to the
// raw entry verbatim; the archive never silently drops a reference.

import { attr, esc } from "./html.js";
import { renderInlineMath } from "./math.js";

export interface ParsedBibEntry {
  type: string;
  key: string;
  fields: Map<string, string>;
}

/** Parse one BibTeX entry. Returns undefined on anything malformed — the
 * caller falls back to showing the source. */
export function parseBibEntry(src: string): ParsedBibEntry | undefined {
  const head = /^\s*@([A-Za-z]+)\s*\{\s*([^\s,{}]*)\s*/.exec(src);
  if (!head) return undefined;
  const type = head[1]!.toLowerCase();
  const key = head[2]!;
  const fields = new Map<string, string>();
  let i = head[0]!.length;

  const skipWs = () => { while (i < src.length && /\s/.test(src[i]!)) i += 1; };
  skipWs();
  while (i < src.length && src[i] !== "}") {
    if (src[i] === ",") { i += 1; skipWs(); continue; }
    const name = /^[A-Za-z][A-Za-z0-9_-]*/.exec(src.slice(i));
    if (!name) return undefined;
    i += name[0].length;
    skipWs();
    if (src[i] !== "=") return undefined;
    i += 1;
    skipWs();
    let value = "";
    if (src[i] === "{") {
      let depth = 0;
      const start = ++i;
      while (i < src.length) {
        if (src[i] === "{") depth += 1;
        else if (src[i] === "}") {
          if (depth === 0) break;
          depth -= 1;
        }
        i += 1;
      }
      if (i >= src.length) return undefined;
      value = src.slice(start, i);
      i += 1;
    } else if (src[i] === '"') {
      const start = ++i;
      while (i < src.length && src[i] !== '"') i += 1;
      if (i >= src.length) return undefined;
      value = src.slice(start, i);
      i += 1;
    } else {
      const bare = /^[^\s,}]+/.exec(src.slice(i));
      if (!bare) return undefined;
      value = bare[0];
      i += bare[0].length;
    }
    fields.set(name[0].toLowerCase(), value.replace(/\s+/g, " ").trim());
    skipWs();
  }
  if (src[i] !== "}") return undefined;
  return { type, key, fields };
}

const COMBINING: Record<string, string> = {
  "'": "́", "`": "̀", "^": "̂", '"': "̈", "~": "̃",
  "=": "̄", ".": "̇", u: "̆", v: "̌", H: "̋",
  c: "̧", d: "̣", b: "̱",
};

const LIGATURES: Record<string, string> = {
  ss: "ß", ae: "æ", AE: "Æ", oe: "œ", OE: "Œ", aa: "å", AA: "Å",
  o: "ø", O: "Ø", l: "ł", L: "Ł",
};

/** Strip TeX markup down to plain text: accents become their Unicode
 * letters, braces and unknown commands vanish. Deliberately lossy beyond
 * that — bibliographies survive it fine. */
function detexFragment(value: string): string {
  return value
    .replace(/\\(['"`^~=.uvHcdb])\s*\{?([A-Za-z])\}?/g,
      (_, cmd: string, ch: string) => (ch + COMBINING[cmd]!).normalize("NFC"))
    .replace(/\\(ss|ae|AE|oe|OE|aa|AA|o|O|l|L)(?![A-Za-z])\s*/g, (_, cmd: string) => LIGATURES[cmd]!)
    .replace(/\\([&%$#_])/g, "$1")
    .replace(/\\[A-Za-z]+\s*/g, "")
    .replace(/[{}]/g, "")
    .replace(/---/g, "—")
    .replace(/--/g, "–")
    .replace(/~/g, " ")
    .replace(/\s+/g, " ");
}

export function detex(value: string): string {
  return detexFragment(value).trim();
}

interface BibTextSegment {
  kind: "text" | "math";
  raw: string;
  value: string;
}

function closingDollar(value: string, start: number, delimiter: "$" | "$$"): number {
  for (let index = start; index < value.length; index += 1) {
    if (!value.startsWith(delimiter, index)) continue;
    if (!escapedAt(value, index)) return index;
  }
  return -1;
}

function escapedAt(value: string, index: number): boolean {
  let slashes = 0;
  for (let before = index - 1; before >= 0 && value[before] === "\\"; before -= 1)
    slashes += 1;
  return slashes % 2 === 1;
}

function closingBrace(value: string, opening: number): number {
  let depth = 1;
  for (let index = opening + 1; index < value.length; index += 1) {
    if (value[index] === "\\") { index += 1; continue; }
    if (value[index] === "{") depth += 1;
    else if (value[index] === "}") {
      depth -= 1;
      if (depth === 0) return index;
    }
  }
  return -1;
}

/** Split a BibTeX field without interpreting prose as math. BibTeX titles
 * conventionally protect capitalization with braces, so prose fragments are
 * still passed through `detex`; only explicit TeX math delimiters and
 * `\ensuremath{...}` become KaTeX. */
function bibTextSegments(value: string): BibTextSegment[] {
  const segments: BibTextSegment[] = [];
  let textStart = 0;
  const flushText = (end: number) => {
    if (end > textStart)
      segments.push({ kind: "text", raw: value.slice(textStart, end), value: value.slice(textStart, end) });
  };
  for (let index = 0; index < value.length;) {
    if (value[index] === "$" && !escapedAt(value, index)) {
      const delimiter: "$" | "$$" = value[index + 1] === "$" ? "$$" : "$";
      const end = closingDollar(value, index + delimiter.length, delimiter);
      if (end >= 0) {
        flushText(index);
        const raw = value.slice(index, end + delimiter.length);
        segments.push({
          kind: "math",
          raw,
          value: value.slice(index + delimiter.length, end).trim(),
        });
        index = end + delimiter.length;
        textStart = index;
        continue;
      }
    }
    if (value.startsWith("\\(", index)) {
      const end = value.indexOf("\\)", index + 2);
      if (end >= 0) {
        flushText(index);
        const raw = value.slice(index, end + 2);
        segments.push({ kind: "math", raw, value: value.slice(index + 2, end).trim() });
        index = end + 2;
        textStart = index;
        continue;
      }
    }
    if (value.startsWith("\\ensuremath", index)) {
      const match = /^\\ensuremath\s*\{/.exec(value.slice(index));
      if (match) {
        const opening = index + match[0].length - 1;
        const end = closingBrace(value, opening);
        if (end >= 0) {
          flushText(index);
          const raw = value.slice(index, end + 1);
          segments.push({ kind: "math", raw, value: value.slice(opening + 1, end).trim() });
          index = end + 1;
          textStart = index;
          continue;
        }
      }
    }
    index += 1;
  }
  flushText(value.length);
  return segments;
}

/** Safe HTML for one bibliography field with embedded TeX rendered by KaTeX.
 * Even `$$...$$` remains inline here: a reference is a sentence, and a
 * display block would break its numbering and punctuation. */
export function renderBibText(value: string): string {
  return bibTextSegments(value.trim()).map((segment) => segment.kind === "math"
    ? renderInlineMath(segment.value, segment.raw)
    : esc(detexFragment(segment.value))).join("");
}

/** "Last, First and von Last, First and ..." → "First Last, First von Last". */
function formatAuthors(raw: string): string {
  const names = raw.split(/\s+and\s+/i).map((name) => {
    const cleaned = detex(name);
    const comma = cleaned.indexOf(",");
    return comma >= 0
      ? `${cleaned.slice(comma + 1).trim()} ${cleaned.slice(0, comma).trim()}`.trim()
      : cleaned;
  }).filter(Boolean);
  if (names.length <= 1) return names[0] ?? "";
  return `${names.slice(0, -1).join(", ")} and ${names[names.length - 1]}`;
}

/** One reference as a list item. Falls back to the raw source in place when
 * the entry does not parse or names no title. */
export function renderBibEntry(src: string): string {
  const parsed = parseBibEntry(src);
  const rawTitle = parsed?.fields.get("title") ?? "";
  if (!parsed || !rawTitle.trim()) return `<li><pre class="bib-entry">${esc(src)}</pre></li>`;
  const field = (name: string) => detex(parsed.fields.get(name) ?? "");
  const renderedField = (name: string) => renderBibText(parsed.fields.get(name) ?? "");

  const pieces: string[] = [];
  const authors = formatAuthors(parsed.fields.get("author") ?? parsed.fields.get("editor") ?? "");
  if (authors) pieces.push(`${esc(authors)}.`);
  pieces.push(`<span class="reference-title">${renderBibText(rawTitle)}</span>.`);

  const venueName = ["journal", "booktitle", "howpublished", "publisher", "school", "institution"]
    .find((name) => field(name));
  const venue = venueName
    ? `${venueName === "booktitle" ? "In " : ""}${renderedField(venueName)}`
    : "";
  const volume = field("volume");
  const number = field("number");
  const pages = field("pages");
  const issue = volume
    ? renderedField("volume") + (number ? `(${renderedField("number")})` : "")
    : renderedField("number");
  const location = [issue, pages ? renderedField("pages") : ""].filter(Boolean).join(":");
  const where = [venue, location].filter(Boolean).join(" ");
  if (where) pieces.push(`${where}${field("year") ? "," : "."}`);
  if (field("year")) pieces.push(`${esc(field("year"))}.`);
  if (field("note")) pieces.push(`${renderedField("note")}.`);

  const links: string[] = [];
  const doi = field("doi").replace(/^https?:\/\/(dx\.)?doi\.org\//, "");
  if (doi) links.push(`<a href="${attr(`https://doi.org/${doi}`)}">doi:${esc(doi)}</a>`);
  const eprint = field("eprint");
  if (eprint && /^arxiv/i.test(field("archiveprefix") || "arxiv"))
    links.push(`<a href="${attr(`https://arxiv.org/abs/${eprint}`)}">arXiv:${esc(eprint)}</a>`);
  const url = parsed.fields.get("url");
  if (url && /^https?:\/\//i.test(url)) links.push(`<a href="${attr(url)}">${esc(url.replace(/^https?:\/\/(www\.)?/, "").replace(/\/$/, ""))}</a>`);
  if (links.length) pieces.push(links.join(" · "));

  return `<li id="ref-${attr(parsed.key)}">${pieces.join(" ")}</li>`;
}
