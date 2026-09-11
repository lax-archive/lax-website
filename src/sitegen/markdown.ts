import { Marked, type Tokens } from "marked";
import { detex } from "./bibtex.js";
import { crossrefExtension } from "./crossref.js";
import { esc } from "./html.js";
import { mathExtension, renderInlineMath } from "./math.js";
import type { SiteModel } from "./model.js";

function safeUrl(href: string): boolean {
  const decoded = href
    .replace(/&#x([0-9a-f]+);?/gi, (_, h: string) => String.fromCodePoint(parseInt(h, 16)))
    .replace(/&#(\d+);?/g, (_, d: string) => String.fromCodePoint(Number(d)))
    .replace(/&colon;/gi, ":");
  let protocol: string;
  try { protocol = new URL(decoded).protocol; }
  catch { return true; }
  return protocol === "http:" || protocol === "https:" || protocol === "mailto:";
}

interface TextToken {
  type: string;
  raw?: string;
  text?: string;
  tokens?: TextToken[];
  items?: TextToken[];
}

function titleTokenText(token: TextToken): string {
  if (token.type === "html") return " ";
  if (token.type === "math" || token.type === "mathBlock") return detex(token.text ?? "");
  if (token.type === "image") return token.text ?? "";
  if (token.type === "br" || token.type === "space" || token.type === "hr") return " ";
  if (token.tokens) return token.tokens.map(titleTokenText).join("");
  if (token.items) return token.items.map(titleTokenText).join(" ");
  return token.text ?? "";
}

/** Safe, markup-free text for browser titles and plain-text labels. */
export function plainAuthorTitle(value: string): string {
  const source = value.replace(
    /\[\[([A-Za-z0-9_.\-']+)(?:\|([^\]\n]+))?\]\]/g,
    (_raw, target: string, label: string | undefined) => label ?? target,
  );
  const parser = new Marked();
  parser.use(mathExtension);
  return (parser.lexer(source) as unknown as TextToken[])
    .map(titleTokenText)
    .join(" ")
    .replace(/[\p{Cc}\p{Cf}]/gu, " ")
    .replace(/\s+/gu, " ")
    .trim()
    .replace(/---/g, "—")
    .replace(/--/g, "–");
}

/** One isolated parser per generated site; author HTML is always text. */
export class MarkdownRenderer {
  constructor(private readonly model: SiteModel) {}

  /** Ordinary Markdown, used for site-owned copy such as the landing page. */
  render(text: string, rootRel: string): string {
    return this.renderWithOptions(text, rootRel, false);
  }

  /** Submission-authored prose: abstracts and concept/proof annotations.
   * TeX may use `$...$`/`$$...$$` or `\(...\)`/`\[...\]`; an inline backtick
   * span is also convenient math shorthand. Fenced code blocks remain
   * ordinary Markdown code blocks. */
  renderAuthorProse(text: string, rootRel: string): string {
    return this.renderWithOptions(text, rootRel, true);
  }

  /** Submission-authored headings: the safe inline subset of the same
   * Markdown and TeX grammar, without paragraph or other block wrappers. */
  renderAuthorInline(text: string, rootRel: string): string {
    return this.renderWithOptions(text, rootRel, true, true);
  }

  /** The authored title grammar reduced to inert text for labels and metadata. */
  plainAuthorTitle(text: string): string {
    return plainAuthorTitle(text);
  }

  private renderWithOptions(text: string, rootRel: string, backtickMath: boolean, inline = false): string {
    const parser = new Marked();
    parser.use(mathExtension, crossrefExtension(this.model, rootRel, !inline), {
      renderer: {
        html(token: Tokens.HTML | Tokens.Tag): string { return esc(token.raw); },
        link(token: Tokens.Link): string | false {
          if (inline) return this.parser.parseInline(token.tokens);
          return safeUrl(token.href) ? false : this.parser.parseInline(token.tokens);
        },
        image(token: Tokens.Image): string | false {
          return inline || !safeUrl(token.href) ? esc(token.text) : false;
        },
        text(token: Tokens.Text | Tokens.Escape): string {
          if ("tokens" in token && token.tokens) return this.parser.parseInline(token.tokens);
          const rendered = "escaped" in token && token.escaped ? token.text : esc(token.text);
          // TeX turns `--` in prose into an en dash. Apply the same convention
          // only to authored text tokens, leaving math, URLs, and code intact.
          return backtickMath ? rendered.replace(/--/g, "–") : rendered;
        },
        codespan(token: Tokens.Codespan): string | false {
          return backtickMath
            ? renderInlineMath(token.text, token.raw)
            : false;
        },
      },
    });
    return (inline ? parser.parseInline(text, { async: false }) : parser.parse(text, { async: false })) as string;
  }
}
