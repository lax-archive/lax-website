import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

function classList(...initial: string[]) {
  const values = new Set(initial);
  return {
    add: (name: string) => values.add(name),
    remove: (name: string) => values.delete(name),
    contains: (name: string) => values.has(name),
  };
}

describe("native front-page submission find", () => {
  it("marks and scrolls to the visible title when a hidden id matches", () => {
    const linkClasses = classList("submissions-list-link");
    const previousClasses = classList("submissions-list-link", "native-find-match");
    const previous = { classList: previousClasses };
    let scrollOptions: unknown;
    const link = {
      classList: linkClasses,
      scrollIntoView: (options: unknown) => { scrollOptions = options; },
    };
    const markerListeners = new Map<string, () => void>();
    const attributes = new Map<string, string>();
    const marker = {
      addEventListener: (name: string, listener: () => void) => markerListeners.set(name, listener),
      closest: (selector: string) => selector === ".submissions-list-link" ? link : null,
      setAttribute: (name: string, value: string) => attributes.set(name, value),
    };
    const timers: Array<{ callback: () => void; delay: number; cleared: boolean }> = [];
    const setTimeout = (callback: () => void, delay: number) => {
      timers.push({ callback, delay, cleared: false });
      return timers.length;
    };
    const clearTimeout = (id?: number) => {
      if (id) timers[id - 1]!.cleared = true;
    };
    const document: any = {
      readyState: "complete",
      getElementById: () => null,
      querySelector: () => null,
      querySelectorAll: (selector: string) => {
        if (selector === "[data-submission-find-alias]") return [marker];
        if (selector === ".submissions-list-link.native-find-match") return [previous];
        return [];
      },
      addEventListener: () => undefined,
    };
    const window: any = {
      matchMedia: () => ({ matches: false }),
      addEventListener: () => undefined,
      location: { search: "" },
    };
    const context: any = { document, window, setTimeout, clearTimeout };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/sidebar.js", "utf8"), context);

    markerListeners.get("beforematch")!();

    expect(previousClasses.contains("native-find-match")).toBe(false);
    expect(linkClasses.contains("native-find-match")).toBe(true);
    expect(scrollOptions).toEqual({ block: "center" });
    timers.find(({ delay }) => delay === 0)!.callback();
    expect(attributes.get("hidden")).toBe("until-found");
    timers.find(({ delay }) => delay === 8000)!.callback();
    expect(linkClasses.contains("native-find-match")).toBe(false);
  });
});
