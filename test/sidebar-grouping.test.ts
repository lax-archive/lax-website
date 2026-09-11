import fs from "node:fs";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

/** Just enough DOM for sidebar.js's filterList: child lists with live
 * insertBefore/nextElementSibling semantics and the handful of selectors the
 * script uses. The insertion order under the group headings is exactly the
 * behavior under test, so the fake must model real child-list moves. */
interface FakeElement {
  id?: string;
  className: string;
  dataset: Record<string, string | undefined>;
  hidden: boolean;
  parent: FakeElement | null;
  children: FakeElement[];
  classList: { contains(name: string): boolean };
  readonly nextElementSibling: FakeElement | null;
  appendChild(child: FakeElement): void;
  insertBefore(child: FakeElement, reference: FakeElement | null): void;
  querySelector(selector: string): FakeElement | null;
  querySelectorAll(selector: string): FakeElement[];
  addEventListener?(name: string, listener: () => void): void;
}

function matches(node: FakeElement, selector: string): boolean {
  const parsed = /^(?:li)?(?:\.([\w-]+))?(?:\[data-([\w-]+)(?:="([^"]*)")?\])?$/.exec(selector.trim());
  if (!parsed) throw new Error(`unsupported selector: ${selector}`);
  const [, className, dataAttribute, dataValue] = parsed;
  if (className && !node.classList.contains(className)) return false;
  if (dataAttribute) {
    const key = dataAttribute.replace(/-([a-z])/g, (_, letter: string) => letter.toUpperCase());
    if (dataValue === undefined) return node.dataset[key] !== undefined;
    return node.dataset[key] === dataValue;
  }
  return Boolean(className) || Boolean(dataAttribute);
}

function element(props: { id?: string; className?: string; dataset?: Record<string, string> } = {}): FakeElement {
  const node = {
    id: props.id,
    className: props.className ?? "",
    dataset: props.dataset ?? {},
    hidden: false,
    parent: null as FakeElement | null,
    children: [] as FakeElement[],
  } as unknown as FakeElement;
  node.classList = { contains: (name) => node.className.split(/\s+/).includes(name) };
  Object.defineProperty(node, "nextElementSibling", {
    get() {
      const siblings = node.parent?.children ?? [];
      const index = siblings.indexOf(node);
      return index >= 0 && index + 1 < siblings.length ? siblings[index + 1]! : null;
    },
  });
  node.appendChild = (child) => node.insertBefore(child, null);
  node.insertBefore = (child, reference) => {
    if (child.parent) child.parent.children.splice(child.parent.children.indexOf(child), 1);
    const index = reference ? node.children.indexOf(reference) : node.children.length;
    node.children.splice(index < 0 ? node.children.length : index, 0, child);
    child.parent = node;
  };
  node.querySelector = (selector) => node.querySelectorAll(selector)[0] ?? null;
  node.querySelectorAll = (selector) => {
    const found = new Set<FakeElement>();
    for (const part of selector.split(",")) {
      for (const child of node.children) if (matches(child, part)) found.add(child);
    }
    return [...found];
  };
  return node;
}

function row(id: string, title: string, state: string, order: number): FakeElement {
  return element({
    dataset: {
      searchTitle: `${id} ${title}`.toLowerCase(),
      searchConcepts: "",
      state,
      searchOrder: String(order),
    },
  });
}

function heading(group: string): FakeElement {
  return element({ className: "entry-heading", dataset: { entryGroup: group } });
}

describe("sidebar grouping during search", () => {
  function harness() {
    const list = element({ id: "entry-list" });
    const empty = element({ id: "entry-list-empty" });
    const registeredHeading = heading("registered");
    const draftHeading = heading("draft");
    const registered = row("lax-2", "new result", "registered", 0);
    const draft = row("lax-3", "newer still", "draft", 1);
    for (const child of [registeredHeading, registered, draftHeading, draft, empty]) {
      list.appendChild(child);
    }

    const searchListeners: Record<string, () => void> = {};
    const searchInput = {
      value: "",
      addEventListener: (name: string, listener: () => void) => { searchListeners[name] = listener; },
    };
    const byId = new Map<string, unknown>([
      ["entry-list", list],
      ["entry-list-empty", empty],
      ["filter-search", searchInput],
    ]);
    const context = {
      document: {
        readyState: "complete",
        getElementById: (id: string) => byId.get(id) ?? null,
        querySelector: () => null,
        querySelectorAll: () => [],
        addEventListener: () => undefined,
      },
      window: {
        matchMedia: () => ({ matches: false }),
        addEventListener: () => undefined,
        location: { search: "" },
      },
    };
    vm.createContext(context);
    vm.runInContext(fs.readFileSync("assets/site/sidebar.js", "utf8"), context);

    const search = (value: string) => {
      searchInput.value = value;
      searchListeners.input!();
    };
    const order = () =>
      list.children.map((child) =>
        child.dataset.entryGroup !== undefined
          ? `#${child.dataset.entryGroup}`
          : child.id === "entry-list-empty"
            ? "#empty"
            : child.dataset.searchTitle!.split(" ")[0]!,
      );
    return { search, order, draftHeading, registeredHeading, registered, draft };
  }

  it("keeps every row under its own heading while filtering", () => {
    const fixture = harness();
    // the empty initial search already sorts and regroups
    expect(fixture.order()).toEqual([
      "#registered", "lax-2", "#draft", "lax-3", "#empty",
    ]);

    // "result" hits the registered title, not the draft.
    fixture.search("result");
    expect(fixture.order()).toEqual([
      "#registered", "lax-2", "#draft", "lax-3", "#empty",
    ]);
    expect(fixture.draft.hidden).toBe(true);
    expect(fixture.draftHeading.hidden).toBe(true);
  });

  it("hides headings whose whole group is filtered away", () => {
    const fixture = harness();
    fixture.search("newer");
    expect(fixture.registered.hidden).toBe(true);
    expect(fixture.registeredHeading.hidden).toBe(true);
    expect(fixture.draft.hidden).toBe(false);
    expect(fixture.draftHeading.hidden).toBe(false);
  });
});
