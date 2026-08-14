import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

describe("Remark42 browser loader", () => {
  it("initializes the canonical thread and loads comments plus the counter", () => {
    const loading = {
      textContent: "Loading discussion…",
      removed: false,
      remove() { this.removed = true; },
    };
    const container = {
      dataset: {
        remark42Host: "https://remark42.example.test/",
        remark42Site: "archive",
        remark42Url: "https://example.test/lax-1/",
      },
    };
    const scripts: Array<Record<string, unknown>> = [];
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : id === "remark42-status" ? loading : null,
      createElement: () => {
        const listeners: Record<string, () => void> = {};
        return {
          noModule: true,
          type: "",
          src: "",
          addEventListener: (name: string, listener: () => void) => { listeners[name] = listener; },
          listeners,
        };
      },
      head: { appendChild: (script: Record<string, unknown>) => scripts.push(script) },
      body: null,
    };
    const windowListeners: Record<string, () => void> = {};
    const window = {
      location: { origin: "https://preview.test", pathname: "/temporary/" },
      addEventListener: (name: string, listener: () => void) => { windowListeners[name] = listener; },
    };
    const context = { document, window };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);

    expect((window as typeof window & { remark_config?: Record<string, unknown> }).remark_config).toMatchObject({
      host: "https://remark42.example.test",
      site_id: "archive",
      url: "https://example.test/lax-1/",
      components: ["embed", "counter"],
      theme: "light",
    });
    expect(scripts.map((script) => script.src)).toEqual([
      "https://remark42.example.test/web/embed.mjs",
      "https://remark42.example.test/web/counter.mjs",
    ]);
    expect(scripts.every((script) => script.type === "module")).toBe(true);

    windowListeners["REMARK42::ready"]!();
    expect(loading.removed).toBe(true);

    (scripts[0]!.listeners as Record<string, () => void>).error!();
    expect(loading.textContent).toBe("Discussion is temporarily unavailable. Please try again later.");
  });
});
