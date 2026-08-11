import katex from "katex";
import type { MarkedExtension, Tokens } from "marked";
import { esc } from "./html.js";

interface MathToken { type: "math" | "mathBlock"; raw: string; text: string }

/** Let a display delimiter on its own source line interrupt the surrounding
 * Markdown paragraph. Authors should not need blank lines around a displayed
 * formula just to make `$$...$$` or `\[...\]` work. */
function firstMathBlockDelimiter(src: string): number | undefined {
  const match = /\n(?=\$\$|\\\[)/.exec(src);
  return match ? match.index + 1 : undefined;
}

function firstMathDelimiter(src: string): number | undefined {
  const indexes = [src.indexOf("$"), src.indexOf("\\(")].filter((index) => index >= 0);
  return indexes.length ? Math.min(...indexes) : undefined;
}

function render(text: string, displayMode: boolean, raw: string): string {
  try {
    return katex.renderToString(text, { displayMode, output: "htmlAndMathml", throwOnError: true, strict: "error" });
  } catch (error) {
    return `<span class="math-error" title="${esc((error as Error).message)}">${esc(raw)}</span>`;
  }
}

/** Render the contents of an inline delimiter as KaTeX. `raw` is retained
 * only for the readable fallback when KaTeX rejects the expression. */
export function renderInlineMath(text: string, raw = `$${text}$`): string {
  return render(text, false, raw);
}

export const mathExtension: MarkedExtension = {
  extensions: [
    {
      name: "mathBlock", level: "block",
      start: firstMathBlockDelimiter,
      tokenizer(src: string): MathToken | undefined {
        const match = /^\$\$[ \t]*\n?([\s\S]+?)\n?[ \t]*\$\$(?:\n|$)/.exec(src)
          ?? /^\\\[[ \t]*\n?([\s\S]+?)\n?[ \t]*\\\](?:\n|$)/.exec(src);
        return match ? { type: "mathBlock", raw: match[0], text: match[1]!.trim() } : undefined;
      },
      renderer(token: Tokens.Generic) {
        const math = token as MathToken;
        return render(math.text, true, math.raw);
      },
    },
    {
      name: "math", level: "inline", start: firstMathDelimiter,
      tokenizer(src: string): MathToken | undefined {
        // Hard-wrapped source is normal, so a span may contain single
        // newlines — but never a blank line, which is a paragraph break.
        const match = /^\$(?!\$)((?:\\.|[^$\n]|\n(?![ \t]*\n))+?)\$(?!\$)/.exec(src)
          ?? /^\\\(((?:[^\n]|\n(?![ \t]*\n))+?)\\\)/.exec(src);
        return match ? { type: "math", raw: match[0], text: match[1]! } : undefined;
      },
      renderer(token: Tokens.Generic) {
        const math = token as MathToken;
        return renderInlineMath(math.text, math.raw);
      },
    },
  ],
};
