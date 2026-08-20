import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

class FakeElement {
  dataset: Record<string, string> = {};
  hidden = false;
  disabled = false;
  textContent = "";
  href = "";
  target = "";
  rel = "";
  className = "";
  dateTime = "";
  attributes = new Map<string, string>();
  children: FakeElement[] = [];
  selectors = new Map<string, FakeElement>();
  listeners = new Map<string, () => void>();

  querySelector(selector: string) { return this.selectors.get(selector) ?? null; }
  addEventListener(name: string, listener: () => void) { this.listeners.set(name, listener); }
  append(...nodes: FakeElement[]) { this.children.push(...nodes); }
  appendChild(node: FakeElement) { this.children.push(node); return node; }
  setAttribute(name: string, value: string) { this.attributes.set(name, value); }
}

const settle = async () => {
  for (let index = 0; index < 5; index += 1) await new Promise((resolve) => setTimeout(resolve, 0));
};

describe("public all-comments activity", () => {
  it("renders newest comments as safe text and links only validated ORCID identities", async () => {
    const root = new FakeElement();
    root.dataset = {
      remark42Host: "https://remark42.example.test",
      remark42Site: "remark",
      identityUrl: "https://remark42.example.test/reactions/v1/identity",
    };
    const list = new FakeElement();
    const status = new FakeElement();
    const more = new FakeElement();
    root.selectors.set("[data-activity-list]", list);
    root.selectors.set("[data-activity-status]", status);
    root.selectors.set("[data-activity-more]", more);
    const oldId = `orcid_${"a".repeat(40)}`;
    const newId = `orcid_${"b".repeat(40)}`;
    const requests: string[] = [];
    const fetch = async (input: URL | string) => {
      const url = String(input);
      requests.push(url);
      if (url.includes("/api/v1/last/1000")) {
        return {
          ok: true,
          json: async () => [
            {
              id: "older", orig: "Earlier comment", text: "<p>Earlier comment</p>", score: -1,
              time: "2026-08-13T10:00:00Z", title: "Lax2",
              locator: { url: "https://laxarchive.org/Lax2/" }, user: { id: oldId, name: "Stale name" },
            },
            {
              id: "newer", orig: "Hello <script>alert(1)</script>", text: "<p>Hello</p>", score: 3,
              time: "2026-08-14T10:00:00Z", title: "Lax2.C",
              locator: { url: "https://laxarchive.org/Lax2/Lax2.C.html" }, user: { id: newId, name: "Old stored name" },
            },
            {
              id: "hidden-review", orig: "🚩 Incorrect claim\n\nlax-review:v2:flag:0:0", text: "<p>🚩 Incorrect claim</p>", score: 0,
              time: "2026-08-15T10:00:00Z", title: "Lax Archive review",
              locator: { url: "https://laxarchive.org/_reactions/Lax2/" }, user: { id: newId, name: "Old stored name" },
            },
          ],
        };
      }
      if (url.includes("/reactions/v1/identities")) {
        return {
          ok: true,
          json: async () => ({
            identities: [{
              remark42_id: newId,
              orcid_id: "0000-0002-1825-0097",
              name: "Current ORCID Name",
            }],
          }),
        };
      }
      return { ok: false, json: async () => ({}) };
    };
    const document = {
      getElementById: (id: string) => id === "all-comments" ? root : null,
      createElement: () => new FakeElement(),
    };
    const context = { document, fetch, URL, Date, setTimeout };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/all-comments.js", "utf8"), context);
    await settle();

    expect(root.attributes.get("aria-busy")).toBe("false");
    expect(list.children).toHaveLength(2);
    const newest = list.children[0]!;
    const newestHeader = newest.children[0]!;
    const newestBody = newest.children[1]!;
    expect(newestHeader.children[0]!.textContent).toBe("Current ORCID Name");
    expect(newestHeader.children[0]!.href).toBe("https://orcid.org/0000-0002-1825-0097");
    expect(newestHeader.children[0]!.target).toBe("_blank");
    expect(newestHeader.children[0]!.rel).toBe("noopener noreferrer");
    expect(newestBody.textContent).toBe("Hello <script>alert(1)</script>");
    expect(list.children[1]!.children[0]!.children[0]!.textContent).toBe("ORCID identity unavailable");
    expect(status.textContent).toBe("Showing all 2 comments.");
    expect(requests.some((url) => url.includes("remark42_id="))).toBe(true);
  });
});
