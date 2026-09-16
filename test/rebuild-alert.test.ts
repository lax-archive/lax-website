import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { alertFor, annotations, ensureIssue, FAILURE_TITLE, readBuildReport, SKIPPED_TITLE } from "../.github/scripts/rebuild-alert.mjs";
import { tmpDir } from "./helpers.js";

const run = "https://github.com/lax-archive/lax-website/actions/runs/1";

describe("the rebuild alert", () => {
  it("reads the build report and annotates every skipped record", () => {
    const dir = tmpDir("lax-rebuild-alert-");
    const file = path.join(dir, "build-report.json");
    fs.writeFileSync(file, JSON.stringify({ records: 86, skipped: [{ id: "lax-7", reason: "concept Lax7.Old declares no type; every concept annotation carries one" }] }));

    const report = readBuildReport(file);

    expect(report).toEqual({ records: 86, skipped: [{ id: "lax-7", reason: expect.stringContaining("declares no type") }] });
    expect(annotations(report)).toEqual(["::warning title=Record skipped::lax-7: concept Lax7.Old declares no type; every concept annotation carries one"]);
    expect(readBuildReport(path.join(dir, "missing.json"))).toEqual({ records: 0, skipped: [] });
  });

  it("has nothing to say when no record was skipped, and names each one when some were", () => {
    expect(alertFor("skipped", run, { records: 87, skipped: [] })).toBeUndefined();
    const alert = alertFor("skipped", run, { records: 86, skipped: [{ id: "lax-7", reason: "bad" }] })!;
    expect(alert.title).toBe(SKIPPED_TITLE);
    expect(alert.body).toContain("left one record out and published the other 86");
    expect(alert.body).toContain("- `lax-7`: bad");
    expect(alert.body).toContain(run);
  });

  it("describes a failed rebuild as a stale site, with the run to look at", () => {
    const alert = alertFor("failure", run)!;
    expect(alert.title).toBe(FAILURE_TITLE);
    expect(alert.body).toContain("stays up, but stale");
    expect(alert.body).toContain(run);
  });

  it("opens one issue per title and never a second while it is open", () => {
    // The schedule fires hourly; the alarm must not.
    const calls: string[][] = [];
    const existing = (args: string[]) => {
      calls.push(args);
      return JSON.stringify([{ number: 4, title: FAILURE_TITLE, url: "https://github.com/lax-archive/lax-website/issues/4" }]);
    };
    expect(ensureIssue(alertFor("failure", run)!, existing)).toEqual({ created: false, url: "https://github.com/lax-archive/lax-website/issues/4" });
    expect(calls).toHaveLength(1);

    const created: Array<[string[], string | undefined]> = [];
    const none = (args: string[], input?: string) => {
      created.push([args, input]);
      return args[0] === "issue" && args[1] === "list" ? "[]" : "https://github.com/lax-archive/lax-website/issues/5\n";
    };
    expect(ensureIssue(alertFor("failure", run)!, none)).toEqual({ created: true, url: "https://github.com/lax-archive/lax-website/issues/5" });
    expect(created[1]![0]).toEqual(["issue", "create", "--title", FAILURE_TITLE, "--body-file", "-"]);
    expect(created[1]![1]).toContain(run);
  });
});
