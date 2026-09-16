import katex from "katex";
import type { MarkedExtension, Tokens } from "marked";
import { esc } from "./html.js";

interface MathToken { type: "math" | "mathBlock"; raw: string; text: string }

/** KaTeX accepts these Unicode symbols but has no metrics for their direct
 * glyphs, leaving zero-height output and logging a warning. Use equivalent
 * supported commands while leaving the authored source and fallback intact. */
function supportedMathSource(text: string): string {
  return text
    .replaceAll("𝓕", "\\mathcal{F}")
    .replaceAll("◇", "\\Diamond");
}

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

function render(text: string, displayMode: boolean, raw: string, errorFallback?: () => string): string {
  try {
    return katex.renderToString(supportedMathSource(text), {
      displayMode,
      output: "htmlAndMathml",
      throwOnError: true,
      // Lean prose naturally uses Unicode mathematical glyphs such as ⊥ and
      // ⊤. KaTeX can render them safely; only their lack of a LaTeX spelling
      // raises `unknownSymbol`. Keep every actual parse/strict error fatal.
      strict: (errorCode) => errorCode === "unknownSymbol" ? "ignore" : "error",
    });
  } catch (error) {
    if (errorFallback) return errorFallback();
    return `<span class="math-error" title="${esc((error as Error).message)}">${esc(raw)}</span>`;
  }
}

/** Render the contents of an inline delimiter as KaTeX. `raw` is retained
 * only for the readable fallback when KaTeX rejects the expression. */
export function renderInlineMath(text: string, raw = `$${text}$`): string {
  return render(text, false, raw);
}

/** Backticks are optional math shorthand in authored prose. If their content
 * is not valid TeX, retain the ordinary inline-code meaning of Markdown. */
export function renderBacktickMath(text: string, raw: string): string {
  return render(text, false, raw, () => `<code>${esc(text)}</code>`);
}

/** Render display math outside Markdown while retaining the same safe,
 * readable error fallback as the Markdown extension. */
export function renderDisplayMath(text: string, raw = `$$${text}$$`): string {
  return render(text, true, raw);
}

/** Tooltips also accept display math inside a single-line title or sentence. */
export const inlineDisplayMathExtension: MarkedExtension = {
  extensions: [{
    name: "inlineDisplayMath", level: "inline",
    start(src: string) {
      const match = /\$\$|\\\[/.exec(src);
      return match?.index;
    },
    tokenizer(src: string): Tokens.Generic | undefined {
      const match = /^\$\$([\s\S]+?)\$\$/.exec(src) ?? /^\\\[([\s\S]+?)\\\]/.exec(src);
      return match ? { type: "inlineDisplayMath", raw: match[0], text: match[1]!.trim() } : undefined;
    },
    renderer(token: Tokens.Generic) {
      return renderDisplayMath(token.text as string, token.raw);
    },
  }],
};

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
        return renderDisplayMath(math.text, math.raw);
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
