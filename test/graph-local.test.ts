import fs from "node:fs";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import { chromium } from "playwright-core";
import { DEFAULT_PROFILE, layoutGraph } from "../src/graph-layout/index.js";
import type { LayoutProfile } from "../src/graph-layout/types.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { prepareGraphs, type LocalGraphDescriptor } from "../src/sitegen/graph-prepare.js";
import { measureDisplayGraph, projectGraph } from "../src/sitegen/graph-project.js";
import { graphSvg } from "../src/sitegen/graph-svg.js";
import { tmpDir } from "./helpers.js";

afterEach(() => { vi.restoreAllMocks(); vi.unstubAllEnvs(); });

const submission = (): SiteSubmission => ({
  record: { specVersion: "1", id: "Lax1", state: "registered", createdAt: "2026-01-01T00:00:00Z" },
  output: { specVersion: "1", id: "Lax1", manifest: { specVersion: "1", id: "Lax1", title: "Alpha", authors: [], bibEntries: [],
    leanVersion: "v4.30.0", mathlibVersion: "abc" }, abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
    concepts: [{ id: "Lax1.Alpha", path: "concepts/Lax1/Alpha.lean", title: "Alpha", type: "definition", description: "",
      imports: [], mathlibImports: [], statements: [], sourceText: "" }] },
});

const raw = { concepts: { nodes: [
  { id: "A", title: "Alpha", href: "A.html" }, { id: "B", title: "Beta", href: "B.html" },
], edges: [{ from: "A", to: "B" }] } };
const page = () => '<!doctype html><html><head><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; script-src \'self\'"></head><body>' +
  '<figure class="graph-figure"><div id="concept-dag" class="figure-container" data-graph="concepts"></div></figure>' +
  `<script type="application/json" id="graph-data">${JSON.stringify(raw)}</script></body></html>`;
const localDescriptor = (html: string): LocalGraphDescriptor => JSON.parse(/<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/u.exec(html)![1]!).local;

describe("local graph host and worker options", () => {
  it.each([undefined, false] as const)("honors an explicit browser path with hostBrowser=%s", async (hostBrowser) => {
    vi.stubEnv("GRAPH_CHROME", undefined);
    // Observe the actual host launch boundary, without running a browser.
    const launch = vi.spyOn(chromium, "launch").mockRejectedValue(new Error("A fixture browser is unavailable"));
    const root = tmpDir("lax-local-options-");
    await generateSite([submission()], path.join(root, "site"), { graphs: { mode: "local", cacheDir: path.join(root, "cache"),
      measurement: { executablePath: "/explicit/graph-browser", ...(hostBrowser === undefined ? {} : { hostBrowser }) } } });
    if (hostBrowser === false) expect(launch).not.toHaveBeenCalled();
    else expect(launch).toHaveBeenCalledExactlyOnceWith(expect.objectContaining({ executablePath: "/explicit/graph-browser" }));
    expect(fs.readFileSync(path.join(root, "site", "Lax1", "index.html"), "utf8")).toContain('data-graph-local="true"');
  });

  it("carries only normalized layout settings in the local descriptor", async () => {
    const profile = { ...DEFAULT_PROFILE, id: "local-wide-v1", portSeparation: 64, rankGap: 80, margin: 48,
      privateSource: "NEVER_TRANSFER_PROFILE_METADATA" };
    const files = new Map([["nested/index.html", page()]]);
    await prepareGraphs(files, { mode: "local", measurement: { hostBrowser: false }, profile });
    const html = files.get("nested/index.html")!, local = localDescriptor(html);
    const { privateSource: _private, ...expected } = profile;
    expect(local.profile).toEqual(expected);
    expect(local.requests).toEqual([{ text: "Alpha", maxWidth: 240 }, { text: "Beta", maxWidth: 240 }]);
    expect(html).not.toContain("NEVER_TRANSFER_PROFILE_METADATA");
    expect(JSON.parse(/<script type="application\/json" id="graph-data">([\s\S]*?)<\/script>/u.exec(html)![1]!)).not.toHaveProperty("profile");
    for (const invalid of [{ ...profile, portSeparation: 0 }, { ...profile, rankPivots: 1.5 }]) {
      const original = page(), unchanged = new Map([["index.html", original]]);
      await expect(prepareGraphs(unchanged, { mode: "local", measurement: { hostBrowser: false }, profile: invalid })).rejects.toThrow("local-graph-profile");
      expect(unchanged.get("index.html")).toBe(original);
    }
  });

  it("uses the requested profile for worker node capacity, placement and digest", async () => {
    const profile: LayoutProfile = { ...DEFAULT_PROFILE, id: "local-wide-v1", portSeparation: 64, rankGap: 80, margin: 48 };
    const display = projectGraph("concepts", raw.concepts);
    const labels = [
      { text: "Alpha", width: 31.734375, height: 16, signature: "alpha-fixture",
        lines: [{ text: "Alpha", x: 0, y: 12, ink: { x: 0, y: 2, width: 31.734375, height: 12 } }] },
      { text: "Beta", width: 24.953125, height: 16, signature: "beta-fixture",
        lines: [{ text: "Beta", x: 0, y: 12, ink: { x: 0, y: 2, width: 24.953125, height: 12 } }] },
    ];
    const oldHandler = Object.getOwnPropertyDescriptor(globalThis, "onmessage"), oldPost = Object.getOwnPropertyDescriptor(globalThis, "postMessage");
    const worker = globalThis as typeof globalThis & { onmessage: (event: { data: unknown }) => void; postMessage: (message: any) => void };
    try {
      await import("../src/sitegen/graph-local-worker.js");
      const draw = async (requested: LayoutProfile): Promise<string> => {
        const messages: any[] = [];
        await new Promise<void>((resolve, reject) => {
          worker.postMessage = (message) => {
            if (message.error) reject(new Error(message.error));
            else if (message.complete) resolve();
            else messages.push(message);
          };
          worker.onmessage({ data: { profile: requested, labels, containers: { "concept-dag": {
            initial: "00", ancestors: 0, descendants: 0, views: { "00": { display, status: "2 concepts" } },
          } } } });
        });
        expect(messages).toHaveLength(1);
        return messages[0].data.views["00"].svg;
      };
      const svg = await draw(profile);
      const measured = measureDisplayGraph(display, new Map(labels.map((label) => [label.text, label])), profile.portSeparation);
      expect(measured.graph.nodes.every((node) => node.width === 128)).toBe(true);
      const inputDigest = /data-layout-digest="([a-f0-9]+)"/u.exec(svg)![1]!;
      const expected = layoutGraph(measured.graph, { inputDigest, profile });
      expect(expected.geometry.profileId).toBe("local-wide-v1");
      expect(svg).toBe(graphSvg(measured, expected.geometry, "concept-dag-00"));
      // A search-budget/profile identity change must also change the digest,
      // even if it happens to select the same coordinate geometry.
      const changed = await draw({ ...profile, id: "local-wide-v2", rankPivots: profile.rankPivots + 1 });
      expect(/data-layout-digest="([a-f0-9]+)"/u.exec(changed)![1]).not.toBe(inputDigest);
    } finally {
      if (oldHandler) Object.defineProperty(globalThis, "onmessage", oldHandler); else delete (globalThis as any).onmessage;
      if (oldPost) Object.defineProperty(globalThis, "postMessage", oldPost); else delete (globalThis as any).postMessage;
    }
  });
});
