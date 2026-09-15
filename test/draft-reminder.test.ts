import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it, vi } from "vitest";

type Listener = (event: { target?: unknown }) => void;

function loadDraftReminder(options: {
  ageDays: number;
  alreadyShown?: boolean;
  nativeDialog?: boolean;
  storageDisabled?: boolean;
}) {
  const now = Date.UTC(2026, 8, 15, 12);
  const createdAt = new Date(now - options.ageDays * 24 * 60 * 60 * 1000).toISOString();
  const attributes = new Set<string>();
  const dialogListeners: Record<string, Listener> = {};
  const closeListeners: Record<string, Listener> = {};
  const values = new Map<string, string>();
  const storageKey = "lax:draft-reminder:lax-7";
  if (options.alreadyShown) values.set(storageKey, "shown");

  const storage = {
    getItem(key: string) {
      if (options.storageDisabled) throw new Error("storage disabled");
      return values.get(key) ?? null;
    },
    setItem(key: string, value: string) {
      if (options.storageDisabled) throw new Error("storage disabled");
      values.set(key, value);
    },
  };
  const closeButton = {
    addEventListener(type: string, listener: Listener) { closeListeners[type] = listener; },
  };
  const dialog: Record<string, any> = {
    dataset: { createdAt, submissionId: "lax-7" },
    querySelector: () => closeButton,
    addEventListener(type: string, listener: Listener) { dialogListeners[type] = listener; },
    setAttribute(name: string) { attributes.add(name); },
    removeAttribute(name: string) { attributes.delete(name); },
  };
  const showModal = vi.fn(() => { attributes.add("open"); });
  const close = vi.fn(() => { attributes.delete("open"); });
  if (options.nativeDialog !== false) Object.assign(dialog, { showModal, close });

  class Clock extends Date {
    static override now() { return now; }
  }
  const context = {
    Date: Clock,
    document: { querySelector: () => dialog },
    window: { sessionStorage: storage },
  };
  vm.createContext(context);
  vm.runInContext(fs.readFileSync("assets/site/draft-reminder.js", "utf8"), context);
  return { attributes, close, closeListeners, dialog, dialogListeners, showModal, storageKey, values };
}

describe("old draft reminder", () => {
  it("does not open before the draft is seven days old", () => {
    const ui = loadDraftReminder({ ageDays: 6.99 });
    expect(ui.showModal).not.toHaveBeenCalled();
    expect(ui.values.has(ui.storageKey)).toBe(false);
  });

  it("opens at seven days and records the reminder for this session", () => {
    const ui = loadDraftReminder({ ageDays: 7 });
    expect(ui.showModal).toHaveBeenCalledOnce();
    expect(ui.values.get(ui.storageKey)).toBe("shown");
  });

  it("does not reopen the same submission during the session", () => {
    const ui = loadDraftReminder({ ageDays: 30, alreadyShown: true });
    expect(ui.showModal).not.toHaveBeenCalled();
  });

  it("still opens when session storage is unavailable", () => {
    const ui = loadDraftReminder({ ageDays: 8, storageDisabled: true });
    expect(ui.showModal).toHaveBeenCalledOnce();
  });

  it("closes from the button or backdrop and supports non-dialog browsers", () => {
    const native = loadDraftReminder({ ageDays: 8 });
    native.closeListeners.click!({});
    expect(native.close).toHaveBeenCalledOnce();

    const fallback = loadDraftReminder({ ageDays: 8, nativeDialog: false });
    expect(fallback.attributes.has("open")).toBe(true);
    fallback.dialogListeners.click!({ target: fallback.dialog });
    expect(fallback.attributes.has("open")).toBe(false);
  });
});
