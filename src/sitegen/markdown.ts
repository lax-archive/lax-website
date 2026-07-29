import { Marked, type Tokens } from "marked";
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

/** One isolated parser per generated site; author HTML is always text. */
export class MarkdownRenderer {
  constructor(private readonly model: SiteModel) {}

  /** Ordinary Markdown, used for site-owned copy such as the landing page. */
  render(text: string, rootRel: string): string {
    return this.renderWithOptions(text, rootRel, false);
  }

  /** Submission-authored prose: abstracts and concept/proof annotations.
   * Alongside `$...$`, an inline backtick span is convenient math shorthand.
   * Fenced code blocks remain ordinary Markdown code blocks. */
  renderAuthorProse(text: string, rootRel: string): string {
    return this.renderWithOptions(text, rootRel, true);
  }

  private renderWithOptions(text: string, rootRel: string, backtickMath: boolean): string {
    const parser = new Marked();
    parser.use(mathExtension, crossrefExtension(this.model, rootRel), {
      renderer: {
        html(token: Tokens.HTML | Tokens.Tag): string { return esc(token.raw); },
        link(token: Tokens.Link): string | false {
          return safeUrl(token.href) ? false : this.parser.parseInline(token.tokens);
        },
        image(token: Tokens.Image): string | false { return safeUrl(token.href) ? false : esc(token.text); },
        codespan(token: Tokens.Codespan): string | false {
          return backtickMath
            ? renderInlineMath(token.text, token.raw)
            : false;
        },
      },
    });
    return parser.parse(text, { async: false }) as string;
  }
}
