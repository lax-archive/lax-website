import { afterEach, describe, expect, it, vi } from "vitest";
import { renderBacktickMath, renderInlineMath } from "../src/sitegen/math.js";

describe("math rendering", () => {
  afterEach(() => vi.restoreAllMocks());

  it("maps unsupported Unicode script and diamond glyphs to measured KaTeX equivalents", () => {
    const warning = vi.spyOn(console, "warn").mockImplementation(() => undefined);

    const inline = renderInlineMath("X ∈ 𝓕 ∪ {◇}");
    const backtick = renderBacktickMath("𝓕", "`𝓕`");

    expect(warning).not.toHaveBeenCalled();
    expect(inline).toContain('<mi mathvariant="script">F</mi>');
    expect(inline).toContain('<mi mathvariant="normal">◊</mi>');
    expect(inline).toContain('class="mord mathcal"');
    expect(inline).toContain('class="mord amsrm"');
    expect(backtick).toContain('<mi mathvariant="script">F</mi>');
  });
});
