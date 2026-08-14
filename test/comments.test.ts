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

  it("loads page reactions with credentials and enables voting for a validated ORCID identity", async () => {
    const count = (value: string) => ({ textContent: value });
    const likeCount = count("0");
    const dislikeCount = count("0");
    const button = (vote: string, counter: { textContent: string }) => {
      const listeners: Record<string, () => void> = {};
      const attributes: Record<string, string> = { "aria-pressed": "false" };
      return {
        dataset: { reactionVote: vote }, disabled: true,
        querySelector: () => counter,
        addEventListener: (name: string, listener: () => void) => { listeners[name] = listener; },
        setAttribute: (name: string, value: string) => { attributes[name] = value; },
        getAttribute: (name: string) => attributes[name],
        listeners,
      };
    };
    const like = button("1", likeCount);
    const dislike = button("-1", dislikeCount);
    const reactionStatus = { textContent: "Loading responses…", dataset: { state: "" } };
    const login = { hidden: false, href: "", textContent: "Sign in with ORCID" };
    const voterList = { children: [] as Array<Record<string, unknown>>, replaceChildren(...nodes: Array<Record<string, unknown>>) { this.children = nodes; } };
    const voterEmpty = { hidden: false };
    const voterPopover = { querySelector: (selector: string) => selector === "ul" ? voterList : selector === "[data-reaction-empty]" ? voterEmpty : null };
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return reactionStatus;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="1"]') return likeCount;
        if (selector === '[data-reaction-count="-1"]') return dislikeCount;
        if (selector === '[data-reaction-voters-popover="1"]') return voterPopover;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction-vote]" ? [like, dislike] : [],
    };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/" } };
    const scripts: Array<Record<string, unknown>> = [];
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : null,
      createElement: (tag: string) => tag === "iframe"
        ? ({ src: "", title: "", hidden: false, contentWindow: null })
        : ({ noModule: true, type: "", src: "", href: "", target: "", rel: "", textContent: "", children: [] as Array<Record<string, unknown>>, addEventListener() {}, appendChild(node: Record<string, unknown>) { this.children.push(node); } }),
      head: { appendChild: (script: Record<string, unknown>) => scripts.push(script) }, body: { appendChild() {} },
    };
    const requests: Array<[string, Record<string, unknown>]> = [];
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/" },
      addEventListener() {},
      fetch: async (url: string, options: Record<string, unknown>) => {
        requests.push([url, options]);
        return { ok: true, json: async () => ({ likes: 4, dislikes: 1, viewer_vote: 1, authenticated: true, eligible: true, viewer: { name: "Alice" }, voters: { likes: [{ name: "Ada Lovelace", orcid: "0000-0002-1825-0097" }], dislikes: [] } }) };
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
    });
  });

  it("uses the authenticated iframe bridge for a partition-safe reaction session", async () => {
    const likeCount = { textContent: "0" };
    const dislikeCount = { textContent: "0" };
    const attributes: Record<string, string> = { "aria-pressed": "false" };
    const listeners: Record<string, (event: unknown) => void> = {};
    const likeListeners: Record<string, () => void> = {};
    const like = {
      dataset: { reactionVote: "1" }, disabled: false,
      addEventListener: (name: string, listener: () => void) => { likeListeners[name] = listener; },
      setAttribute: (name: string, value: string) => { attributes[name] = value; },
      getAttribute: (name: string) => attributes[name],
    };
    const dislike = {
      dataset: { reactionVote: "-1" }, disabled: false,
      addEventListener() {}, setAttribute() {}, getAttribute: () => "false",
    };
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="1"]') return likeCount;
        if (selector === '[data-reaction-count="-1"]') return dislikeCount;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction-vote]" ? [like, dislike] : [],
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
            data: { likes: 2, dislikes: 0, viewer_vote: 0, authenticated: true, eligible: true, viewer: { name: "Ada" }, voters: { likes: [], dislikes: [] } },
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
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/", assign() {} },
      addEventListener: (name: string, listener: (event: unknown) => void) => { listeners[name] = listener; },
      setTimeout, clearTimeout,
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
    expect(directFetches).toBe(0);
    expect(likeCount.textContent).toBe("2");
    expect(status.textContent).toBe("Signed in as Ada");
  });
});
