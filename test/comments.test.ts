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
      querySelector: () => null,
      createElement: (tag: string) => {
        if (tag === "iframe") return { src: "", title: "", hidden: false, contentWindow: null };
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
      body: { appendChild() {} },
    };
    const windowListeners: Record<string, () => void> = {};
    const window = {
      location: { origin: "https://preview.test", pathname: "/temporary/" },
      addEventListener: (name: string, listener: () => void) => { windowListeners[name] = listener; },
    };
    const context = { document, window, URL };
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

  it("loads page reactions with credentials and enables reactions for a validated ORCID identity", async () => {
    const count = (value: string) => ({ textContent: value });
    const likeCount = count("0");
    const dislikeCount = count("0");
    const button = (reaction: string, counter: { textContent: string }) => {
      const listeners: Record<string, () => void> = {};
      const attributes: Record<string, string> = { "aria-pressed": "false" };
      return {
        dataset: { reaction }, disabled: true,
        querySelector: () => counter,
        addEventListener: (name: string, listener: () => void) => { listeners[name] = listener; },
        setAttribute: (name: string, value: string) => { attributes[name] = value; },
        getAttribute: (name: string) => attributes[name],
        listeners,
      };
    };
    const like = button("like", likeCount);
    const dislike = button("dislike", dislikeCount);
    const reactionStatus = { textContent: "Loading responses…", dataset: { state: "" } };
    const login = { hidden: false, href: "", textContent: "Sign in with ORCID" };
    const voterList = { children: [] as Array<Record<string, unknown>>, replaceChildren(...nodes: Array<Record<string, unknown>>) { this.children = nodes; } };
    const voterEmpty = { hidden: false };
    const voterPopover = { querySelector: (selector: string) => selector === "ul" ? voterList : selector === "[data-reaction-empty]" ? voterEmpty : null };
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return reactionStatus;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="like"]') return likeCount;
        if (selector === '[data-reaction-count="dislike"]') return dislikeCount;
        if (selector === '[data-reaction-voters-popover="like"]') return voterPopover;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [like, dislike] : [],
    };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/" } };
    const scripts: Array<Record<string, unknown>> = [];
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : null,
      createElement: (tag: string) => tag === "iframe"
        ? ({ src: "", title: "", hidden: false, contentWindow: null })
        : ({ noModule: true, type: "", src: "", href: "", target: "", rel: "", textContent: "", children: [] as Array<Record<string, unknown>>, attributes: {} as Record<string, string>, addEventListener() {}, setAttribute(name: string, value: string) { this.attributes[name] = value; }, appendChild(node: Record<string, unknown>) { this.children.push(node); } }),
      head: { appendChild: (script: Record<string, unknown>) => scripts.push(script) }, body: { appendChild() {} },
    };
    const requests: Array<[string, Record<string, unknown>]> = [];
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/" },
      addEventListener() {},
      sessionStorage: { getItem: () => null, setItem() {}, removeItem() {} },
      fetch: async (url: string, options: Record<string, unknown>) => {
        requests.push([url, options]);
        return { ok: true, json: async () => ({ counts: { like: 4, dislike: 1, rocket: 2 }, viewer_reaction: "like", authenticated: true, eligible: true, viewer: { name: "Alice" }, voters: { like: [{ name: "Ada Lovelace", orcid: "0000-0002-1825-0097" }], dislike: [], rocket: [] } }) };
      },
    };
    const context = { document, window, URL };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    await new Promise((resolve) => setImmediate(resolve));

    expect(requests[0]?.[0]).toContain("/reactions/v1/page?url=https%3A%2F%2Flaxarchive.org%2FLax2%2F");
    expect(requests[0]?.[1]).toMatchObject({ credentials: "include" });
    expect(like.disabled).toBe(false);
    expect(dislike.disabled).toBe(false);
    expect(like.getAttribute("aria-pressed")).toBe("true");
    expect(likeCount.textContent).toBe("4");
    expect(dislikeCount.textContent).toBe("1");
    expect(reactionStatus.textContent).toBe("Signed in as Alice");
    expect(login.hidden).toBe(true);
    const voterLink = voterList.children[0]!.children as Array<Record<string, unknown>>;
    expect(voterLink[0]).toMatchObject({
      href: "https://orcid.org/0000-0002-1825-0097",
      target: "_blank",
      rel: "noopener noreferrer",
      textContent: "Ada Lovelace",
      title: "Ada Lovelace — ORCID iD 0000-0002-1825-0097",
    });
  });

  it("uses the authenticated iframe bridge for a partition-safe reaction session", async () => {
    const likeCount = { textContent: "0" };
    const dislikeCount = { textContent: "0" };
    const attributes: Record<string, string> = { "aria-pressed": "false" };
    const listeners: Record<string, (event: unknown) => void> = {};
    const likeListeners: Record<string, () => void> = {};
    const like = {
      dataset: { reaction: "like" }, disabled: false,
      addEventListener: (name: string, listener: () => void) => { likeListeners[name] = listener; },
      setAttribute: (name: string, value: string) => { attributes[name] = value; },
      getAttribute: (name: string) => attributes[name],
    };
    const dislike = {
      dataset: { reaction: "dislike" }, disabled: false,
      addEventListener() {}, setAttribute() {}, getAttribute: () => "false",
    };
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="like"]') return likeCount;
        if (selector === '[data-reaction-count="dislike"]') return dislikeCount;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [like, dislike] : [],
    };
    const posted: Array<{ message: Record<string, unknown>; origin: string }> = [];
    const bridgeWindow = {
      postMessage(message: Record<string, unknown>, origin: string) {
        posted.push({ message, origin });
        queueMicrotask(() => listeners.message?.({
          origin,
          source: bridgeWindow,
          data: {
            source: "lax-reactions", id: message.id, ok: true, status: 200,
            data: { counts: { like: 2, dislike: 0, rocket: 0 }, viewer_reaction: "", authenticated: true, eligible: true, viewer: { name: "Ada" }, voters: { like: [], dislike: [], rocket: [] } },
          },
        }));
      },
    };
    const iframe = { src: "", title: "", hidden: false, contentWindow: bridgeWindow };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/" } };
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : null,
      createElement: (tag: string) => tag === "iframe" ? iframe : ({ noModule: true, type: "", src: "", addEventListener() {} }),
      head: { appendChild() {} }, body: { appendChild() {} },
    };
    let directFetches = 0;
    let pendingReactionCleared = false;
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/", assign() {} },
      addEventListener: (name: string, listener: (event: unknown) => void) => { listeners[name] = listener; },
      setTimeout, clearTimeout,
      sessionStorage: { getItem: () => "like", setItem() {}, removeItem() { pendingReactionCleared = true; } },
      fetch: async () => { directFetches += 1; throw new Error("direct transport must not be used"); },
    };
    const context = { document, window, URL, setTimeout, clearTimeout, queueMicrotask };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    listeners.message!({ origin: "https://remark42.example.test", source: bridgeWindow, data: { source: "lax-reactions", type: "ready" } });
    await new Promise((resolve) => setTimeout(resolve, 0));
    await new Promise((resolve) => setTimeout(resolve, 0));

    expect(iframe.src).toBe("https://remark42.example.test/reactions/v1/bridge");
    expect(iframe.hidden).toBe(true);
    expect(posted[0]).toMatchObject({
      origin: "https://remark42.example.test",
      message: { source: "lax-reactions", action: "page", url: "https://laxarchive.org/Lax2/" },
    });
    expect(posted[1]).toMatchObject({
      origin: "https://remark42.example.test",
      message: { source: "lax-reactions", action: "reaction", url: "https://laxarchive.org/Lax2/", reaction: "like" },
    });
    expect(pendingReactionCleared).toBe(true);
    expect(directFetches).toBe(0);
    expect(likeCount.textContent).toBe("2");
    expect(status.textContent).toBe("Signed in as Ada");
  });

  it("requests the shared popup login instead of navigating away for a signed-out reaction", async () => {
    const listeners: Record<string, () => void> = {};
    const attributes: Record<string, string> = { "aria-pressed": "false" };
    const like = {
      dataset: { reaction: "like" }, disabled: true,
      addEventListener: (name: string, listener: () => void) => { listeners[name] = listener; },
      setAttribute: (name: string, value: string) => { attributes[name] = value; },
      getAttribute: (name: string) => attributes[name],
    };
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const count = { textContent: "0" };
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="like"]') return count;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [like] : [],
    };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/" } };
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : null,
      createElement: (tag: string) => tag === "iframe"
        ? ({ src: "", title: "", hidden: false, contentWindow: null })
        : ({ noModule: true, type: "", src: "", addEventListener() {} }),
      head: { appendChild() {} }, body: { appendChild() {} },
    };
    let assigned = "";
    let pending = "";
    let loginRequested = false;
    class FakeCustomEvent {
      constructor(public type: string, public init: { cancelable?: boolean }) {}
    }
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/", assign: (value: string) => { assigned = value; } },
      addEventListener() {},
      dispatchEvent: (event: FakeCustomEvent) => { loginRequested = event.type === "LAX::login-request" && event.init.cancelable === true; return false; },
      sessionStorage: { getItem: () => null, setItem: (_key: string, value: string) => { pending = value; }, removeItem() {} },
      fetch: async () => ({ ok: true, status: 200, json: async () => ({ counts: { like: 0, dislike: 0, rocket: 0 }, viewer_reaction: "", authenticated: false, eligible: false, voters: { like: [], dislike: [], rocket: [] } }) }),
    };
    const context = { document, window, URL, CustomEvent: FakeCustomEvent };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    await new Promise((resolve) => setImmediate(resolve));

    expect(like.disabled).toBe(false);
    await listeners.click!();
    expect(pending).toBe("like");
    expect(loginRequested).toBe(true);
    expect(assigned).toBe("");
  });
});
