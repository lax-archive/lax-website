// The deploy workflow's alarm. Two things used to go unnoticed: a production
// rebuild failing (the site stays up but stale, and the hourly fallback
// fails the same way, silently) and a record the build left out. Both now
// become one open issue in this repository — one, because the schedule
// fires every hour and an alarm that repeats is an alarm nobody reads. A
// maintainer closes the issue when the cause is fixed; the next alert opens
// a new one only if none is open under the same title.
//
//   rebuild-alert.mjs failure <run-url> [--issue]
//   rebuild-alert.mjs skipped <run-url> <build-report.json> [--issue]
//
// Without --issue (branch previews) the alert is printed and annotated only.

import fs from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

export const FAILURE_TITLE = "Website rebuild failed";
export const SKIPPED_TITLE = "Website build skipped records";

/** The report `site:build --build-report` writes, or an empty one. */
export function readBuildReport(file) {
  if (file === undefined || !fs.existsSync(file)) return { records: 0, skipped: [] };
  const parsed = JSON.parse(fs.readFileSync(file, "utf8"));
  const skipped = Array.isArray(parsed.skipped) ? parsed.skipped : [];
  return {
    records: Number.isInteger(parsed.records) ? parsed.records : 0,
    skipped: skipped.filter((entry) => entry && typeof entry.id === "string" && typeof entry.reason === "string"),
  };
}

/** One workflow annotation per skipped record, so the run itself shows them. */
export function annotations(report) {
  return report.skipped.map((entry) => `::warning title=Record skipped::${entry.id}: ${entry.reason.replace(/\r?\n/g, " ")}`);
}

/** The issue to open, or undefined when there is nothing to report. */
export function alertFor(kind, runUrl, report = { records: 0, skipped: [] }) {
  if (kind === "failure") {
    return {
      title: FAILURE_TITLE,
      body: [
        "A production rebuild of the website did not complete, so the site is serving whatever the last successful rebuild published — it stays up, but stale, and every later rebuild (the database dispatch and the hourly fallback alike) fails the same way until the cause is fixed.",
        "",
        `Run: ${runUrl}`,
        "",
        "Close this issue once a rebuild goes green. A failed run opens a new issue only while none with this title is open.",
      ].join("\n"),
    };
  }
  if (kind === "skipped") {
    if (report.skipped.length === 0) return undefined;
    const list = report.skipped.map((entry) => `- \`${entry.id}\`: ${entry.reason}`).join("\n");
    return {
      title: SKIPPED_TITLE,
      body: [
        `The website build left ${report.skipped.length === 1 ? "one record" : `${report.skipped.length} records`} out and published the other ${report.records}. A skipped record has no page; everything else is current.`,
        "",
        list,
        "",
        `Run: ${runUrl}`,
        "",
        "The archive validated each record fail-closed before publishing, so a skip is corruption in `lax-database` to be fixed there (`npm run admin -- revalidate <id>` in the `lax` repository, or a delete). Close this issue once the build reports no skips; a build that still skips opens a new issue only while none with this title is open.",
      ].join("\n"),
    };
  }
  throw new Error(`unknown alert kind ${JSON.stringify(kind)}`);
}

function gh(args, input) {
  return execFileSync("gh", args, { encoding: "utf8", input, stdio: ["pipe", "pipe", "inherit"] });
}

/** Open the issue unless one with the same title is already open. */
export function ensureIssue(alert, run = gh) {
  const open = JSON.parse(run(["issue", "list", "--state", "open", "--limit", "100", "--json", "number,title,url"]));
  const existing = open.find((issue) => issue.title === alert.title);
  if (existing) return { created: false, url: existing.url };
  const url = run(["issue", "create", "--title", alert.title, "--body-file", "-"], alert.body).trim();
  return { created: true, url };
}

function main() {
  const args = process.argv.slice(2);
  const issue = args.includes("--issue");
  const [kind, runUrl, reportFile] = args.filter((argument) => argument !== "--issue");
  if (kind === undefined || runUrl === undefined) {
    console.error("usage: rebuild-alert.mjs failure <run-url> [--issue] | skipped <run-url> <build-report.json> [--issue]");
    process.exit(2);
  }
  const report = kind === "skipped" ? readBuildReport(reportFile) : undefined;
  const alert = alertFor(kind, runUrl, report);
  if (alert === undefined) {
    console.log("nothing to report");
    return;
  }
  if (report) for (const line of annotations(report)) console.log(line);
  if (process.env.GITHUB_STEP_SUMMARY) {
    fs.appendFileSync(process.env.GITHUB_STEP_SUMMARY, `### ${alert.title}\n\n${alert.body}\n\n`);
  }
  if (!issue) {
    console.log(`${alert.title} (no issue opened for this run)`);
    return;
  }
  const result = ensureIssue(alert);
  console.log(`${result.created ? "opened" : "already open"}: ${result.url}`);
}

if (process.argv[1] && fileURLToPath(import.meta.url) === fs.realpathSync(process.argv[1])) main();
