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

  it("loads page reactions with credentials and enables voting only for a validated ORCID identity", async () => {
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
    const reactions = {
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return reactionStatus;
        if (selector === "[data-reactions-login]") return login;
        return null;
      },
      querySelectorAll: () => [like, dislike],
    };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/" } };
    const scripts: Array<Record<string, unknown>> = [];
    const document = {
      getElementById: (id: string) => id === "remark42" ? container : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : null,
      createElement: () => ({ noModule: true, type: "", src: "", addEventListener() {} }),
      head: { appendChild: (script: Record<string, unknown>) => scripts.push(script) }, body: null,
    };
    const requests: Array<[string, Record<string, unknown>]> = [];
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/", href: "https://laxarchive.org/Lax2/" },
      addEventListener() {},
      fetch: async (url: string, options: Record<string, unknown>) => {
        requests.push([url, options]);
        return { ok: true, json: async () => ({ likes: 4, dislikes: 1, viewer_vote: 1, authenticated: true, eligible: true, viewer: { name: "Alice" }, voters: { likes: [], dislikes: [] } }) };
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
  });
});
