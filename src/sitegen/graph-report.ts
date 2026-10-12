import fs from "node:fs";
import path from "node:path";
import type { GraphPreparationResult, GraphPreparationDiagnostic, GraphPreparationStatistics } from "./graph-prepare.js";

/** Spool detail rows instead of retaining a build's algorithm reports. The
 * final JSON has the same shape as the in-memory report and is installed only
 * after successful preparation. None of these files enter the published tree. */
export class GraphReportWriter {
  private directory: string;
  private diagnostics: number;
  private layouts: number;
  private counts = { diagnostics: 0, layouts: 0 };

  constructor(private file: string) {
    file = path.resolve(file);
    this.file = file;
    fs.mkdirSync(path.dirname(file), { recursive: true });
    this.directory = fs.mkdtempSync(path.join(path.dirname(file), ".graph-report-"));
    const opened: number[] = [];
    try {
      this.diagnostics = fs.openSync(path.join(this.directory, "diagnostics"), "w");
      opened.push(this.diagnostics);
      this.layouts = fs.openSync(path.join(this.directory, "layouts"), "w");
    } catch (error) {
      for (const fd of opened) fs.closeSync(fd);
      fs.rmSync(this.directory, { recursive: true, force: true });
      throw error;
    }
  }

  diagnostic(value: GraphPreparationDiagnostic): void { this.row("diagnostics", value); }
  layout(value: GraphPreparationStatistics["layouts"][number]): void { this.row("layouts", value); }

  private row(kind: "diagnostics" | "layouts", value: unknown): void {
    fs.writeFileSync(this[kind], (this.counts[kind]++ ? ",\n" : "") + JSON.stringify(value));
  }

  finish(result: GraphPreparationResult): void {
    const file = path.join(this.directory, "report.json"), out = fs.openSync(file, "w");
    const copy = (kind: "diagnostics" | "layouts") => {
      const input = fs.openSync(path.join(this.directory, kind), "r");
      try {
        const buffer = Buffer.allocUnsafe(64 * 1024);
        let bytes: number;
        while ((bytes = fs.readSync(input, buffer)) > 0) fs.writeFileSync(out, buffer.subarray(0, bytes));
      } finally { fs.closeSync(input); }
    };
    try {
      fs.writeFileSync(out, `{"localFallback":${result.localFallback},"diagnostics":[\n`);
      copy("diagnostics");
      const { layouts: _layouts, ...statistics } = result.statistics;
      fs.writeFileSync(out, `\n],"statistics":${JSON.stringify(statistics).slice(0, -1)},"layouts":[\n`);
      copy("layouts");
      fs.writeFileSync(out, "\n]}}\n");
    } finally { fs.closeSync(out); }
    fs.renameSync(file, this.file);
  }

  close(): void {
    fs.closeSync(this.diagnostics); fs.closeSync(this.layouts);
    fs.rmSync(this.directory, { recursive: true, force: true });
  }
}
