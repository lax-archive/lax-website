import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it, vi } from "vitest";

type Listener = (event: { target?: unknown }) => void;

function loadVersionHistory(nativeDialog: boolean) {
  const buttonListeners: Record<string, Listener> = {};
  const dialogListeners: Record<string, Listener> = {};
  const closeListeners: Record<string, Listener> = {};
  const attributes = new Set<string>();
  const closeButton = {
    addEventListener: (type: string, listener: Listener) => { closeListeners[type] = listener; },
  };
  const dialog: Record<string, unknown> = {
    querySelector: () => closeButton,
    addEventListener: (type: string, listener: Listener) => { dialogListeners[type] = listener; },
    setAttribute: (name: string) => { attributes.add(name); },
    removeAttribute: (name: string) => { attributes.delete(name); },
  };
  const showModal = vi.fn(() => { attributes.add("open"); });
  const close = vi.fn(() => { attributes.delete("open"); });
  if (nativeDialog) Object.assign(dialog, { showModal, close });
  const button = {
    addEventListener: (type: string, listener: Listener) => { buttonListeners[type] = listener; },
  };
  const context = {
    document: {
      querySelector: (selector: string) => selector === "[data-version-dialog]" ? dialog : button,
    },
  };
  vm.createContext(context);
  vm.runInContext(fs.readFileSync("assets/site/version-history.js", "utf8"), context);
  return { attributes, buttonListeners, closeListeners, dialogListeners, dialog, showModal, close };
}

describe("version history dialog", () => {
  it("opens and closes a native dialog", () => {
    const ui = loadVersionHistory(true);
    ui.buttonListeners.click!({});
    expect(ui.showModal).toHaveBeenCalledOnce();
    ui.closeListeners.click!({});
    expect(ui.close).toHaveBeenCalledOnce();
  });

  it("falls back to the open attribute and closes from the backdrop", () => {
    const ui = loadVersionHistory(false);
    ui.buttonListeners.click!({});
    expect(ui.attributes.has("open")).toBe(true);
    ui.dialogListeners.click!({ target: ui.dialog });
    expect(ui.attributes.has("open")).toBe(false);
  });
});
