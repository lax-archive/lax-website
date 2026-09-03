import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

describe("front-page submission pagination", () => {
  it("shows ten rows at a time and resets when the search changes", () => {
    const rows = Array.from({ length: 25 }, (_, index) => ({
      dataset: {
        searchTitle: `submission needle${index}`,
        searchConcepts: "",
        searchOrder: String(index),
        state: "registered",
        tags: "|all|",
      } as Record<string, string | undefined>,
      hidden: false,
      setAttribute(name: string, value: string) {
        if (name === "hidden") this.hidden = true;
        (this as any)[name] = value;
      },
    }));
    const empty = { hidden: true };
    const children: any[] = [...rows, empty];
    const submissions = {
      querySelectorAll(selector: string) {
        if (selector === "li[data-search], li[data-search-title]" || selector === "li[data-search-title]") return rows;
        return [];
      },
      querySelector() { return null; },
      insertBefore(row: any, reference: any) {
        const current = children.indexOf(row);
        if (current >= 0) children.splice(current, 1);
        children.splice(children.indexOf(reference), 0, row);
      },
    };
    const searchListeners = new Map<string, () => void>();
    const search = {
      value: "",
      addEventListener(name: string, listener: () => void) { searchListeners.set(name, listener); },
    };
    const buttonListeners = new Map<string, () => void>();
    const buttonAttributes = new Map<string, string>();
    const button = {
      hidden: true,
      addEventListener(name: string, listener: () => void) { buttonListeners.set(name, listener); },
      setAttribute(name: string, value: string) { buttonAttributes.set(name, value); },
    };
    const status = { textContent: "" };
    const byId = new Map<string, any>([
      ["submissions-list", submissions],
      ["submissions-list-empty", empty],
      ["submissions-load-more", button],
      ["tag-results-status", status],
      ["filter-search", search],
    ]);
    const document = {
      readyState: "complete",
      fonts: undefined,
      getElementById: (id: string) => byId.get(id) ?? null,
      querySelector: () => null,
      querySelectorAll: () => [],
      addEventListener: () => undefined,
    };
    const window = {
      matchMedia: () => ({ matches: false }),
      addEventListener: () => undefined,
      location: { search: "" },
    };
    const context = {
      CSS: { escape: (value: string) => value },
      document,
      window,
      URLSearchParams,
      cancelAnimationFrame: () => undefined,
      requestAnimationFrame: (callback: () => void) => callback(),
    };

    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/sidebar.js", "utf8"), context);

    const visibleCount = () => rows.filter((row) => !row.hidden).length;
    expect(visibleCount()).toBe(10);
    expect(button.hidden).toBe(false);
    expect(buttonAttributes.get("aria-label")).toBe("Load 10 more submissions");
    expect(status.textContent).toBe("Showing 10 of 25 submissions.");

    buttonListeners.get("click")!();
    expect(visibleCount()).toBe(20);
    expect(button.hidden).toBe(false);
    expect(buttonAttributes.get("aria-label")).toBe("Load 5 more submissions");
    expect(status.textContent).toBe("Showing 20 of 25 submissions.");

    buttonListeners.get("click")!();
    expect(visibleCount()).toBe(25);
    expect(button.hidden).toBe(true);
    expect(status.textContent).toBe("Showing 25 submissions.");

    search.value = "needle24";
    searchListeners.get("input")!();
    expect(visibleCount()).toBe(1);
    expect(button.hidden).toBe(true);
    expect(status.textContent).toBe("Showing 1 submission matching your search.");

    search.value = "";
    searchListeners.get("input")!();
    expect(visibleCount()).toBe(10);
    expect(button.hidden).toBe(false);
  });
});
