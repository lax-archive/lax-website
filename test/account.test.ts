import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

class FakeElement {
  dataset: Record<string, string> = {};
  hidden = false;
  disabled = false;
  textContent = "";
  href = "";
  title = "";
  className = "";
  dateTime = "";
  attributes = new Map<string, string>();
  children: FakeElement[] = [];
  selectors = new Map<string, FakeElement>();
  listeners = new Map<string, (event?: { target?: FakeElement }) => void>();
  opened = false;

  querySelector(selector: string) { return this.selectors.get(selector) ?? null; }
  addEventListener(name: string, listener: (event?: { target?: FakeElement }) => void) { this.listeners.set(name, listener); }
  append(...nodes: FakeElement[]) { this.children.push(...nodes); }
  appendChild(node: FakeElement) { this.children.push(node); return node; }
  replaceChildren(...nodes: FakeElement[]) { this.children = nodes; }
  setAttribute(name: string, value: string) { this.attributes.set(name, value); }
  removeAttribute(name: string) { this.attributes.delete(name); }
  showModal() { this.opened = true; }
  close() { this.opened = false; }
}

const settle = async () => {
  await new Promise((resolve) => setTimeout(resolve, 0));
  await new Promise((resolve) => setTimeout(resolve, 0));
};

function fixture(user: { id: string; name: string }) {
  const root = new FakeElement();
  root.dataset = {
    remark42Host: "https://remark42.example.test",
    remark42Site: "remark",
    identityUrl: "https://remark42.example.test/reactions/v1/identity",
  };
  const dialog = new FakeElement();
  const login = new FakeElement();
  const loginLabel = new FakeElement();
  loginLabel.textContent = "Sign in with ORCID";
  login.selectors.set("span:last-child", loginLabel);
  const settings = new FakeElement();
  const settingsLabel = new FakeElement();
  settingsLabel.textContent = "Settings";
  settings.selectors.set("span:last-child", settingsLabel);
  settings.hidden = true;
  root.selectors.set("[data-account-login]", login);
  root.selectors.set("[data-account-settings]", settings);

  const elements: Record<string, FakeElement> = {
    "[data-account-close]": new FakeElement(),
    "[data-account-content]": new FakeElement(),
    "[data-account-status]": new FakeElement(),
    "[data-account-name]": new FakeElement(),
    "[data-account-id]": new FakeElement(),
    "[data-account-avatar]": new FakeElement(),
    "[data-account-refresh]": new FakeElement(),
    "[data-account-logout]": new FakeElement(),
    "[data-account-comments]": new FakeElement(),
    "[data-account-comments-status]": new FakeElement(),
    "[data-account-comment-count]": new FakeElement(),
  };
  for (const [selector, element] of Object.entries(elements)) dialog.selectors.set(selector, element);

  const requests: string[] = [];
  const fetch = async (input: URL | string) => {
    const url = String(input);
    requests.push(url);
    if (url.includes("/api/v1/user")) return { ok: true, json: async () => user };
    if (url.includes("/reactions/v1/identity")) {
      return {
        ok: true,
        json: async () => ({
          remark42_id: user.id,
          orcid_id: "0000-0002-1825-0097",
          name: user.name,
        }),
      };
    }
    if (url.includes("/api/v1/comments")) return { ok: true, json: async () => ({ comments: [], count: 0 }) };
    return { ok: true, json: async () => ({}) };
  };
  const events: Array<{ type: string; detail: unknown }> = [];
  const listeners: Record<string, (event: Record<string, unknown>) => void> = {};
  class FakeCustomEvent {
    constructor(public type: string, public init: { detail: unknown }) {}
    get detail() { return this.init.detail; }
  }
  const window = {
    location: { href: "https://laxarchive.org/Lax2/?view=test#discussion" },
    dispatchEvent: (event: FakeCustomEvent) => { events.push({ type: event.type, detail: event.detail }); },
    addEventListener: (name: string, listener: (event: Record<string, unknown>) => void) => { listeners[name] = listener; },
    setTimeout,
    clearTimeout,
  };
  const bridgeWindow = {
    postMessage(message: Record<string, unknown>, origin: string) {
      queueMicrotask(() => listeners.message?.({
        origin,
        source: bridgeWindow,
        data: {
          source: "lax-reactions",
          id: message.id,
          ok: true,
          status: 200,
          data: message.action === "me"
            ? { authenticated: true, eligible: true, viewer: { remark42_id: user.id, orcid_id: "0000-0002-1825-0097", name: user.name, profile_url: "https://orcid.org/0000-0002-1825-0097" } }
            : message.action === "comments" ? { comments: [], count: 0 } : {},
        },
      }));
    },
  };
  const iframe = Object.assign(new FakeElement(), { contentWindow: bridgeWindow, src: "" });
  const document = {
    querySelector: (selector: string) => selector === "[data-account-root]" ? root : null,
    getElementById: (id: string) => id === "account-dialog" ? dialog : null,
    createElement: (tag: string) => tag === "iframe" ? iframe : new FakeElement(),
    body: new FakeElement(),
    head: new FakeElement(),
  };
  return { root, dialog, login, loginLabel, settings, settingsLabel, elements, requests, events, fetch, window, document, FakeCustomEvent, listeners, bridgeWindow };
}

describe("ORCID account header", () => {
  it("shows Settings for a named session and links the validated raw ORCID iD", async () => {
    const fx = fixture({ id: `orcid_${"a".repeat(40)}`, name: "Ada Lovelace" });
    const context = { document: fx.document, window: fx.window, fetch: fx.fetch, URL, CustomEvent: fx.FakeCustomEvent, Date, setTimeout };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/account.js", "utf8"), context);
    fx.listeners.message!({ origin: "https://remark42.example.test", source: fx.bridgeWindow, data: { source: "lax-reactions", type: "ready" } });
    await settle();

    expect(fx.login.hidden).toBe(true);
    expect(fx.settings.hidden).toBe(false);
    expect(fx.settingsLabel.textContent).toBe("Ada Lovelace");
    expect(fx.elements["[data-account-name]"]!.textContent).toBe("Ada Lovelace");
    expect(fx.elements["[data-account-name]"]!.href).toBe("https://orcid.org/0000-0002-1825-0097");
    expect(fx.login.href).toContain(encodeURIComponent("https://laxarchive.org/Lax2/?view=test#discussion"));

    fx.settings.listeners.get("click")!();
    expect(fx.dialog.opened).toBe(true);
    await settle();
    expect(fx.elements["[data-account-comments-status]"]!.textContent).toBe("You have not posted any comments yet.");
  });

  it("blocks an unnamed Remark42 fallback session in the account UI", async () => {
    const fx = fixture({ id: `orcid_${"b".repeat(40)}`, name: "noname_abcd" });
    const context = { document: fx.document, window: fx.window, fetch: fx.fetch, URL, CustomEvent: fx.FakeCustomEvent, Date, setTimeout };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/account.js", "utf8"), context);
    fx.listeners.message!({ origin: "https://remark42.example.test", source: fx.bridgeWindow, data: { source: "lax-reactions", type: "ready" } });
    await settle();

    expect(fx.login.hidden).toBe(false);
    expect(fx.settings.hidden).toBe(true);
    expect(fx.loginLabel.textContent).toBe("Sign in with ORCID");
    expect(fx.elements["[data-account-status]"]!.textContent).toContain("public name shared by ORCID is required");
  });
});
