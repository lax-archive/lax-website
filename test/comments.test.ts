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

  it("loads public reviews with credentials and enables them for a validated ORCID identity", async () => {
    const count = (value: string) => ({ textContent: value });
    const endorseCount = count("0");
    const flagCount = count("0");
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
    const endorse = button("endorse", endorseCount);
    const flag = button("flag", flagCount);
    const reactionStatus = { textContent: "Loading review…", dataset: { state: "" } };
    const login = { hidden: false, href: "", textContent: "Sign in with ORCID" };
    const voterList = { children: [] as Array<Record<string, unknown>>, replaceChildren(...nodes: Array<Record<string, unknown>>) { this.children = nodes; } };
    const voterEmpty = { hidden: false };
    const voterPopover = { querySelector: (selector: string) => selector === "ul" ? voterList : selector === "[data-reaction-empty]" ? voterEmpty : null };
    const reactions = {
      dataset: { reviewKind: "submission", sourceLines: "0" },
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return reactionStatus;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="endorse"]') return endorseCount;
        if (selector === '[data-reaction-count="flag"]') return flagCount;
        if (selector === '[data-reaction-voters-popover="endorse"]') return voterPopover;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [endorse, flag] : [],
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
        return { ok: true, json: async () => ({ counts: { endorse: 4, flag: 1 }, viewer_reaction: "endorse", authenticated: true, eligible: true, viewer: { name: "Alice" }, flags: [], voters: { endorse: [{ name: "Ada Lovelace", orcid: "0000-0002-1825-0097" }], flag: [] } }) };
      },
    };
    const context = { document, window, URL };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    await new Promise((resolve) => setImmediate(resolve));

    expect(requests[0]?.[0]).toContain("/reactions/v1/page?url=https%3A%2F%2Flaxarchive.org%2FLax2%2F");
    expect(requests[0]?.[1]).toMatchObject({ credentials: "include" });
    expect(endorse.disabled).toBe(false);
    expect(flag.disabled).toBe(false);
    expect(endorse.getAttribute("aria-pressed")).toBe("true");
    expect(endorseCount.textContent).toBe("4");
    expect(flagCount.textContent).toBe("1");
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

  it("renders public flag explanations and their validated concept source ranges", async () => {
    const classList = () => {
      const values = new Set<string>();
      return {
        add: (...names: string[]) => names.forEach((name) => values.add(name)),
        remove: (...names: string[]) => names.forEach((name) => values.delete(name)),
        contains: (name: string) => values.has(name),
        toggle: (name: string, force?: boolean) => {
          const enabled = force ?? !values.has(name);
          if (enabled) values.add(name); else values.delete(name);
          return enabled;
        },
      };
    };
    const element = () => ({
      id: "", className: "", type: "", href: "", target: "", rel: "", title: "", textContent: "", hidden: false,
      dataset: {} as Record<string, string>, attributes: {} as Record<string, string>, children: [] as Array<Record<string, any>>,
      classList: classList(),
      addEventListener() {},
      setAttribute(name: string, value: string) { this.attributes[name] = value; },
      appendChild(node: Record<string, any>) { this.children.push(node); },
      append(...nodes: Array<Record<string, any>>) { this.children.push(...nodes); },
      replaceChildren(...nodes: Array<Record<string, any>>) { this.children = nodes; },
    });
    const row2 = element();
    const row3 = element();
    const railHost = element();
    const flagList = element();
    const flagEmpty = element();
    const endorseCount = { textContent: "0" };
    const flagCount = { textContent: "0" };
    const reviewButton = (reaction: string) => ({
      dataset: { reaction }, disabled: true,
      addEventListener() {}, setAttribute() {}, getAttribute: () => "false",
    });
    const endorse = reviewButton("endorse");
    const flag = reviewButton("flag");
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const reactions = {
      dataset: { reviewKind: "concept", sourceLines: "4" },
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === "[data-flag-list]") return flagList;
        if (selector === "[data-flag-list-empty]") return flagEmpty;
        if (selector === '[data-reaction-count="endorse"]') return endorseCount;
        if (selector === '[data-reaction-count="flag"]') return flagCount;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [endorse, flag] : [],
    };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/Lax2.C.html" } };
    const scripts: Array<Record<string, unknown>> = [];
    const document = {
      documentElement: { classList: classList() },
      getElementById: (id: string) => id === "remark42" ? container : id === "L2" ? row2 : id === "L3" ? row3 : null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions : selector === "[data-source-review-rails]" ? railHost : null,
      querySelectorAll: (selector: string) => selector.startsWith(".inline-contract-table tr.") ? [row2, row3] : [],
      createElement: (tag: string) => tag === "iframe"
        ? ({ src: "", title: "", hidden: false, contentWindow: null })
        : ({ ...element(), noModule: true, type: "", src: "" }),
      head: { appendChild: (script: Record<string, unknown>) => scripts.push(script) }, body: { appendChild() {} },
    };
    class FakeCustomEvent { constructor(public type: string) {} }
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/Lax2.C.html", href: "https://laxarchive.org/Lax2/Lax2.C.html" },
      addEventListener() {}, dispatchEvent() {},
      sessionStorage: { getItem: () => null, setItem() {}, removeItem() {} },
      fetch: async () => ({
        ok: true, status: 200,
        json: async () => ({
          counts: { endorse: 0, flag: 1 }, viewer_reaction: "", authenticated: true, eligible: true,
          viewer: { name: "Alice" }, voters: { endorse: [], flag: [] },
          flags: [{
            id: "flag-1", message: "The conclusion needs another hypothesis.", line_start: 2, line_end: 3,
            time: "2026-08-19T12:00:00Z", author: { name: "Ada Lovelace", orcid: "0000-0002-1825-0097" },
          }],
        }),
      }),
    };
    const context = { document, window, URL, CustomEvent: FakeCustomEvent };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    await new Promise((resolve) => setImmediate(resolve));

    expect(flagCount.textContent).toBe("1");
    expect(flagEmpty.hidden).toBe(true);
    expect(flagList.children).toHaveLength(1);
    expect(flagList.children[0]).toMatchObject({ id: "review-flag-flag-1", className: "flag-list-item" });
    const flagMeta = flagList.children[0]!.children[0]!.children[0]!;
    expect(flagMeta).toMatchObject({
      href: "https://orcid.org/0000-0002-1825-0097", target: "_blank", rel: "noopener noreferrer", textContent: "Ada Lovelace",
    });
    expect(flagList.children[0]!.children[1]).toMatchObject({ textContent: "The conclusion needs another hypothesis." });
    expect(flagList.children[0]!.children[2]).toMatchObject({ textContent: "Go to lines 2–3" });
    expect(row2.classList.contains("line-flagged")).toBe(true);
    expect(row3.classList.contains("line-flagged")).toBe(true);
    expect(railHost.children).toHaveLength(1);
    expect(railHost.children[0]!.dataset).toMatchObject({ sourceLine: "L2" });
    expect(railHost.children[0]!.children[0]).toMatchObject({ textContent: "🚩" });
  });

  it("uses the authenticated iframe bridge for a partition-safe review session", async () => {
    const endorseCount = { textContent: "0" };
    const flagCount = { textContent: "0" };
    const attributes: Record<string, string> = { "aria-pressed": "false" };
    const listeners: Record<string, (event: unknown) => void> = {};
    const endorseListeners: Record<string, () => void> = {};
    const flagListeners: Record<string, () => Promise<void> | void> = {};
    const flagFormListeners: Record<string, (event: { preventDefault(): void }) => Promise<void> | void> = {};
    const endorse = {
      dataset: { reaction: "endorse" }, disabled: false,
      addEventListener: (name: string, listener: () => void) => { endorseListeners[name] = listener; },
      setAttribute: (name: string, value: string) => { attributes[name] = value; },
      getAttribute: (name: string) => attributes[name],
    };
    const flag = {
      dataset: { reaction: "flag" }, disabled: false,
      addEventListener: (name: string, listener: () => Promise<void> | void) => { flagListeners[name] = listener; },
      setAttribute() {}, getAttribute: () => "false",
    };
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const flagMessage = { value: "", focus() {} };
    const flagFormStatus = { textContent: "" };
    const flagRemoveListeners: Record<string, () => Promise<void> | void> = {};
    const flagRemove = {
      hidden: true,
      addEventListener(name: string, listener: () => Promise<void> | void) { flagRemoveListeners[name] = listener; },
    };
    const flagLineStart = { value: "", addEventListener() {} };
    const flagLineEnd = { value: "", addEventListener() {} };
    const flagLineSelection = { textContent: "" };
    const flagLinePickerListeners: Record<string, () => void> = {};
    const flagLinePicker = {
      textContent: "Select lines from source",
      addEventListener(name: string, listener: () => void) { flagLinePickerListeners[name] = listener; },
    };
    const fakeClassList = () => {
      const values = new Set<string>();
      return {
        add: (...names: string[]) => names.forEach((name) => values.add(name)),
        remove: (...names: string[]) => names.forEach((name) => values.delete(name)),
        contains: (name: string) => values.has(name),
        toggle: (name: string, force?: boolean) => {
          const enabled = force ?? !values.has(name);
          if (enabled) values.add(name); else values.delete(name);
          return enabled;
        },
      };
    };
    const sourceRows = new Map([2, 3, 4].map((line) => [line, { classList: fakeClassList() }]));
    const sourceLink = (line: number) => {
      const handlers: Record<string, (event: { preventDefault(): void }) => void> = {};
      return {
        handlers,
        getAttribute: (name: string) => name === "href" ? `#L${line}` : null,
        addEventListener: (name: string, listener: (event: { preventDefault(): void }) => void) => { handlers[name] = listener; },
      };
    };
    const line2 = sourceLink(2);
    const line4 = sourceLink(4);
    let flagEditorOpen = false;
    let flagEditorCloseListener: (() => void) | undefined;
    const flagEditor = {
      showModal() { flagEditorOpen = true; },
      close() { flagEditorOpen = false; flagEditorCloseListener?.(); },
      addEventListener(name: string, listener: () => void) { if (name === "close") flagEditorCloseListener = listener; },
    };
    const flagForm = {
      addEventListener(name: string, listener: (event: { preventDefault(): void }) => Promise<void> | void) { flagFormListeners[name] = listener; },
    };
    const reactions = {
      dataset: { reviewKind: "concept", sourceLines: "4" },
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === "[data-flag-editor]") return flagEditor;
        if (selector === "[data-flag-form]") return flagForm;
        if (selector === "[data-flag-message]") return flagMessage;
        if (selector === "[data-flag-form-status]") return flagFormStatus;
        if (selector === "[data-flag-remove]") return flagRemove;
        if (selector === "[data-flag-line-start]") return flagLineStart;
        if (selector === "[data-flag-line-end]") return flagLineEnd;
        if (selector === "[data-flag-line-selection]") return flagLineSelection;
        if (selector === "[data-flag-line-picker]") return flagLinePicker;
        if (selector === '[data-reaction-count="endorse"]') return endorseCount;
        if (selector === '[data-reaction-count="flag"]') return flagCount;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [endorse, flag] : [],
    };
    const posted: Array<{ message: Record<string, unknown>; origin: string }> = [];
    let bridgeAuthenticated = true;
    let currentReview = "";
    const respondToBridge = (source: Record<string, unknown>, message: Record<string, unknown>, origin: string) => {
        posted.push({ message, origin });
        if (message.action === "reaction") currentReview = message.reaction === "clear" ? "" : String(message.reaction || "");
        const viewerFlag = currentReview === "flag" ? {
          id: "flag-1", message: String(message.message || ""), author: { name: "Ada", orcid: "0000-0002-1825-0097" },
          line_start: Number(message.line_start || 0), line_end: Number(message.line_end || 0), time: "2026-08-19T12:00:00Z",
        } : null;
        queueMicrotask(() => listeners.message?.({
          origin,
          source,
          data: {
            source: "lax-reactions", id: message.id, ok: true, status: 200,
            data: bridgeAuthenticated
              ? { counts: { endorse: currentReview === "endorse" ? 2 : 1, flag: currentReview === "flag" ? 1 : 0 }, viewer_reaction: currentReview, viewer_flag: viewerFlag, authenticated: true, eligible: true, viewer: { name: "Ada" }, flags: viewerFlag ? [viewerFlag] : [], voters: { endorse: [], flag: [] } }
              : { counts: { endorse: 2, flag: 0 }, viewer_reaction: "", authenticated: false, eligible: false, flags: [], voters: { endorse: [], flag: [] } },
          },
        }));
    };
    const bridgeWindow = {
      postMessage(message: Record<string, unknown>, origin: string) { respondToBridge(bridgeWindow, message, origin); },
    };
    const remarkBridgeWindow = {
      postMessage(message: Record<string, unknown>, origin: string) { respondToBridge(remarkBridgeWindow, message, origin); },
    };
    const iframe = { src: "", title: "", hidden: false, contentWindow: bridgeWindow };
    const remarkFrame = { contentWindow: remarkBridgeWindow };
    const container = { dataset: { remark42Host: "https://remark42.example.test", remark42Site: "remark", remark42Url: "https://laxarchive.org/Lax2/Lax2.C.html" } };
    const document = {
      documentElement: { classList: fakeClassList() },
      getElementById: (id: string) => id === "remark42" ? container : sourceRows.get(Number(id.replace(/^L/, ""))) || null,
      querySelector: (selector: string) => selector === "[data-reactions-host]" ? reactions
        : selector === "#remark42 iframe" ? remarkFrame
        : selector === ".inline-contract-table" ? { scrollIntoView() {} } : null,
      querySelectorAll: (selector: string) => selector === ".inline-contract-table .line-num a" ? [line2, line4]
        : selector.includes("line-pending-flag") ? [...sourceRows.values()] : [],
      createElement: (tag: string) => tag === "iframe" ? iframe : ({ noModule: true, type: "", src: "", addEventListener() {} }),
      head: { appendChild() {} }, body: { appendChild() {} },
    };
    let directFetches = 0;
    let pendingReactionCleared = false;
    const window = {
      location: { origin: "https://laxarchive.org", pathname: "/Lax2/Lax2.C.html", href: "https://laxarchive.org/Lax2/Lax2.C.html", assign() {} },
      addEventListener: (name: string, listener: (event: unknown) => void) => { listeners[name] = listener; },
      setTimeout, clearTimeout,
      sessionStorage: { getItem: () => "endorse", setItem() {}, removeItem() { pendingReactionCleared = true; } },
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
      message: { source: "lax-reactions", action: "page", url: "https://laxarchive.org/Lax2/Lax2.C.html" },
    });
    expect(posted[1]).toMatchObject({
      origin: "https://remark42.example.test",
      message: { source: "lax-reactions", action: "reaction", url: "https://laxarchive.org/Lax2/Lax2.C.html", reaction: "endorse" },
    });
    expect(pendingReactionCleared).toBe(true);
    expect(directFetches).toBe(0);
    expect(endorseCount.textContent).toBe("2");
    expect(status.textContent).toBe("Signed in as Ada");

    const pageRequestsBeforeRemark = posted.filter((entry) => entry.message.action === "page").length;
    for (let index = 0; index < 4; index += 1) {
      listeners.message!({ origin: "https://remark42.example.test", source: remarkBridgeWindow, data: { source: "lax-reactions", type: "ready" } });
    }
    await new Promise((resolve) => setTimeout(resolve, 0));
    await new Promise((resolve) => setTimeout(resolve, 0));
    expect(posted.filter((entry) => entry.message.action === "page")).toHaveLength(pageRequestsBeforeRemark + 1);

    await flagListeners.click!();
    expect(flagEditorOpen).toBe(true);
    await flagFormListeners.submit!({ preventDefault() {} });
    expect(flagFormStatus.textContent).toBe("Explain what appears incorrect before publishing the flag.");
    expect(posted.filter((entry) => entry.message.reaction === "flag")).toHaveLength(0);

    flagMessage.value = "The conclusion needs another hypothesis.";
    flagLinePickerListeners.click!();
    expect(flagEditorOpen).toBe(false);
    expect(flagLinePicker.textContent).toBe("Cancel line selection");
    line2.handlers.click!({ preventDefault() {} });
    expect(sourceRows.get(2)!.classList.contains("line-pending-flag")).toBe(true);
    listeners.keydown!({ key: "Escape", preventDefault() {} });
    expect(flagEditorOpen).toBe(true);
    expect(flagLineStart.value).toBe("");
    expect(flagLineEnd.value).toBe("");

    flagLinePickerListeners.click!();
    line2.handlers.click!({ preventDefault() {} });
    line4.handlers.click!({ preventDefault() {} });
    expect(flagEditorOpen).toBe(true);
    expect(flagLineStart.value).toBe("2");
    expect(flagLineEnd.value).toBe("4");
    expect(flagLineSelection.textContent).toBe("Lines 2–4 selected.");
    await flagFormListeners.submit!({ preventDefault() {} });
    expect(posted.at(-1)).toMatchObject({ message: {
      source: "lax-reactions", action: "reaction", url: "https://laxarchive.org/Lax2/Lax2.C.html", reaction: "flag",
      message: "The conclusion needs another hypothesis.", line_start: 2, line_end: 4,
    } });
    expect(flagEditorOpen).toBe(false);
    expect(flagCount.textContent).toBe("1");
    expect(status.textContent).toBe("Signed in as Ada");

    await flagListeners.click!();
    expect(flagEditorOpen).toBe(true);
    expect(flagMessage.value).toBe("The conclusion needs another hypothesis.");
    expect(flagLineStart.value).toBe(2);
    expect(flagLineEnd.value).toBe(4);
    expect(flagRemove.hidden).toBe(false);
    await flagRemoveListeners.click!();
    expect(posted.at(-1)).toMatchObject({ message: {
      source: "lax-reactions", action: "reaction", url: "https://laxarchive.org/Lax2/Lax2.C.html", reaction: "clear",
    } });
    expect(flagEditorOpen).toBe(false);
    expect(flagCount.textContent).toBe("0");

    bridgeAuthenticated = false;
    listeners.message!({ origin: "https://remark42.example.test", source: remarkBridgeWindow, data: { source: "lax-reactions", type: "session-change" } });
    await new Promise((resolve) => setTimeout(resolve, 0));
    await new Promise((resolve) => setTimeout(resolve, 0));
    expect(posted.at(-1)).toMatchObject({ message: { source: "lax-reactions", action: "page", url: "https://laxarchive.org/Lax2/Lax2.C.html" } });
    expect(status.textContent).toBe("Sign in with ORCID to review.");
    expect(login.hidden).toBe(false);
  });

  it("requests the shared login instead of navigating away for a signed-out endorsement", async () => {
    const listeners: Record<string, () => void> = {};
    const attributes: Record<string, string> = { "aria-pressed": "false" };
    const endorse = {
      dataset: { reaction: "endorse" }, disabled: true,
      addEventListener: (name: string, listener: () => void) => { listeners[name] = listener; },
      setAttribute: (name: string, value: string) => { attributes[name] = value; },
      getAttribute: (name: string) => attributes[name],
    };
    const status = { textContent: "", dataset: { state: "" } };
    const login = { hidden: false, href: "" };
    const count = { textContent: "0" };
    const reactions = {
      dataset: { reviewKind: "submission", sourceLines: "0" },
      querySelector: (selector: string) => {
        if (selector === "[data-reactions-status]") return status;
        if (selector === "[data-reactions-login]") return login;
        if (selector === '[data-reaction-count="endorse"]') return count;
        return null;
      },
      querySelectorAll: (selector: string) => selector === "[data-reaction]" ? [endorse] : [],
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
      fetch: async () => ({ ok: true, status: 200, json: async () => ({ counts: { endorse: 0, flag: 0 }, viewer_reaction: "", authenticated: false, eligible: false, flags: [], voters: { endorse: [], flag: [] } }) }),
    };
    const context = { document, window, URL, CustomEvent: FakeCustomEvent };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/comments.js", "utf8"), context);
    await new Promise((resolve) => setImmediate(resolve));

    expect(endorse.disabled).toBe(false);
    await listeners.click!();
    expect(pending).toBe("endorse");
    expect(loginRequested).toBe(true);
    expect(assigned).toBe("");
  });
});
