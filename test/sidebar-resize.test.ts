import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

describe("desktop sidebar resizing", () => {
  it("resizes by pointer, clamps the width, and persists the result", () => {
    const listeners: Record<string, (event: Record<string, unknown>) => void> = {};
    const attributes = new Map<string, string>();
    const classes = new Set<string>();
    const properties = new Map<string, string>();
    const storage = new Map<string, string>([["lax-sidebar-width", "340"]]);
    let capturedPointer: number | undefined;
    let resizeEvents = 0;

    const sidebar = {};
    const resizer = {
      addEventListener: (name: string, listener: (event: Record<string, unknown>) => void) => {
        listeners[name] = listener;
      },
      setAttribute: (name: string, value: string) => attributes.set(name, value),
      setPointerCapture: (pointerId: number) => { capturedPointer = pointerId; },
      hasPointerCapture: (pointerId: number) => capturedPointer === pointerId,
      releasePointerCapture: (pointerId: number) => {
        if (capturedPointer === pointerId) capturedPointer = undefined;
      },
    };
    const byId = new Map<string, unknown>([
      ["sidebar", sidebar],
      ["sidebar-resizer", resizer],
    ]);
    const context = {
      document: {
        readyState: "complete",
        documentElement: { style: { setProperty: (name: string, value: string) => properties.set(name, value) } },
        body: {
          classList: {
            add: (name: string) => classes.add(name),
            remove: (name: string) => classes.delete(name),
          },
        },
        getElementById: (id: string) => byId.get(id) ?? null,
        querySelector: () => null,
        querySelectorAll: () => [],
        addEventListener: () => undefined,
      },
      window: {
        matchMedia: () => ({ matches: false }),
        addEventListener: () => undefined,
        dispatchEvent: () => { resizeEvents += 1; },
        location: { search: "" },
      },
      localStorage: {
        getItem: (key: string) => storage.get(key) ?? null,
        setItem: (key: string, value: string) => storage.set(key, value),
      },
      Event: class Event { constructor(readonly type: string) {} },
    };

    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/sidebar.js", "utf8"), context);

    expect(properties.get("--sidebar-width")).toBe("340px");
    expect(attributes.get("aria-valuenow")).toBe("340");

    const preventDefault = () => undefined;
    listeners.pointerdown!({ button: 0, clientX: 340, pointerId: 7, preventDefault });
    expect(classes.has("sidebar-resizing")).toBe(true);
    expect(capturedPointer).toBe(7);
    listeners.pointermove!({ clientX: 460 });
    expect(properties.get("--sidebar-width")).toBe("460px");
    listeners.pointerup!({ pointerId: 7 });

    expect(classes.has("sidebar-resizing")).toBe(false);
    expect(capturedPointer).toBeUndefined();
    expect(storage.get("lax-sidebar-width")).toBe("460");
    expect(resizeEvents).toBe(1);

    listeners.pointerdown!({ button: 0, clientX: 460, pointerId: 8, preventDefault });
    listeners.pointermove!({ clientX: 900 });
    expect(properties.get("--sidebar-width")).toBe("520px");
    listeners.pointerup!({ pointerId: 8 });
  });

  it("supports arrow and boundary keys", () => {
    const listeners: Record<string, (event: Record<string, unknown>) => void> = {};
    let width = "";
    let ariaNow = "";
    let stored = "";
    const resizer = {
      addEventListener: (name: string, listener: (event: Record<string, unknown>) => void) => {
        listeners[name] = listener;
      },
      setAttribute: (name: string, value: string) => { if (name === "aria-valuenow") ariaNow = value; },
    };
    const context = {
      document: {
        readyState: "complete",
        documentElement: { style: { setProperty: (_name: string, value: string) => { width = value; } } },
        body: { classList: { add: () => undefined, remove: () => undefined } },
        getElementById: (id: string) => id === "sidebar" ? {} : id === "sidebar-resizer" ? resizer : null,
        querySelector: () => null,
        querySelectorAll: () => [],
        addEventListener: () => undefined,
      },
      window: {
        matchMedia: () => ({ matches: false }),
        addEventListener: () => undefined,
        dispatchEvent: () => undefined,
        location: { search: "" },
      },
      localStorage: {
        getItem: () => null,
        setItem: (_key: string, value: string) => { stored = value; },
      },
      Event: class Event { constructor(readonly type: string) {} },
    };

    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/sidebar.js", "utf8"), context);
    const press = (key: string, shiftKey = false) => listeners.keydown!({ key, shiftKey, preventDefault: () => undefined });

    press("ArrowRight");
    expect(width).toBe("295px");
    press("ArrowLeft", true);
    expect(width).toBe("263px");
    press("Home");
    expect(width).toBe("220px");
    press("End");
    expect(width).toBe("520px");
    expect(ariaNow).toBe("520");
    expect(stored).toBe("520");
  });
});
