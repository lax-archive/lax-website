// A small, tolerant BibTeX renderer: submission manifests carry raw BibTeX
// entries, and the References section shows them compiled — authors, italic
// title, venue, year, links — the way a paper's bibliography reads, not as
// source code. Anything the parser cannot make sense of falls back to the
// raw entry verbatim; the archive never silently drops a reference.

import { attr, esc } from "./html.js";

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
export function detex(value: string): string {
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
    .replace(/\s+/g, " ")
    .trim();
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
  const title = parsed && detex(parsed.fields.get("title") ?? "");
  if (!parsed || !title) return `<li><pre class="bib-entry">${esc(src)}</pre></li>`;
  const field = (name: string) => detex(parsed.fields.get(name) ?? "");

  const pieces: string[] = [];
  const authors = formatAuthors(parsed.fields.get("author") ?? parsed.fields.get("editor") ?? "");
  if (authors) pieces.push(`${esc(authors)}.`);
  pieces.push(`<span class="reference-title">${esc(title)}</span>.`);

  const venue = field("journal") || (field("booktitle") && `In ${field("booktitle")}`)
    || field("howpublished") || field("publisher") || field("school") || field("institution");
  const volume = field("volume");
  const number = field("number");
  const pages = field("pages");
  const issue = volume ? volume + (number ? `(${number})` : "") : number;
  const where = [venue, [issue, pages].filter(Boolean).join(":")].filter(Boolean).join(" ");
  if (where) pieces.push(`${esc(where)}${field("year") ? "," : "."}`);
  if (field("year")) pieces.push(`${esc(field("year"))}.`);
  if (field("note")) pieces.push(`${esc(field("note"))}.`);

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
