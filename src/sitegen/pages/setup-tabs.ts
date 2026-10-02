import { attr, esc } from "../html.js";
import type { MarkdownRenderer } from "../markdown.js";

interface SetupTabsOptions {
  idPrefix: string;
  contentPage?: boolean;
}

/** One accessible setup selector shared by the front page and the full guide. */
export function setupTabs(
  source: string,
  markdown: MarkdownRenderer,
  rootRel: string,
  options: SetupTabsOptions,
): string {
  const ids = new Map([["Linux / macOS", "unix"], ["Windows", "windows"]]);
  const tabs = source.trim().split(/\n(?=### )/).map((chunk) => {
    const match = /^### ([^\n]+)\n+([\s\S]+)$/u.exec(chunk.trim());
    if (!match) throw new Error(`invalid setup tab: ${chunk}`);
    const label = match[1]!.trim();
    const id = ids.get(label);
    if (!id) throw new Error(`unsupported setup tab: ${label}`);
    return { id, label, body: match[2]!.trim() };
  });
  for (const label of ids.keys())
    if (!tabs.some((tab) => tab.label === label)) throw new Error(`setup.md is missing the ${label} tab`);

  const controls = tabs.map(({ id, label }, index) => {
    const tabId = `${options.idPrefix}-${id}-tab`;
    const panelId = `${options.idPrefix}-${id}-panel`;
    return `<button class="landing-setup-tab" type="button" role="tab" id="${attr(tabId)}" aria-selected="${index === 0}" aria-controls="${attr(panelId)}" tabindex="${index === 0 ? 0 : -1}">${esc(label)}</button>`;
  });
  const panels = tabs.map(({ id, body }, index) => {
    const tabId = `${options.idPrefix}-${id}-tab`;
    const panelId = `${options.idPrefix}-${id}-panel`;
    return `<div class="landing-setup-panel landing-section-copy latex-content" id="${attr(panelId)}" role="tabpanel" aria-labelledby="${attr(tabId)}"${index === 0 ? "" : " hidden"}>
${markdown.render(body, rootRel)}
</div>`;
  });
  const contentClass = options.contentPage ? " content-setup" : "";
  return `<div class="landing-setup-tabs${contentClass}" data-setup-tabs>
<div class="landing-setup-tab-list" role="tablist" aria-label="Choose your operating system">
${controls.join("\n")}
</div>
${panels.join("\n")}
</div>`;
}
