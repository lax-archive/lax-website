/** Batched preparation between page composition and final file emission.
 * This stage only sees the permission-filtered presentation JSON in pages. */
import fs from "node:fs";
import path from "node:path";
import { createHash, randomUUID } from "node:crypto";
import { performance } from "node:perf_hooks";
import { layoutGraph, SELECTION_POLICY, type LayoutResult } from "../graph-layout/index.js";
import { canonicalJson, compareText, deepFreeze } from "../graph-layout/normalize.js";
import { DEFAULT_PROFILE, ENGINE_VERSION, GEOMETRY_SCHEMA_VERSION, GraphDiagnosticError,
  type Diagnostic, type GraphGeometry, type GeometryMetrics, type LayoutProfile } from "../graph-layout/types.js";
import { validateGeometry } from "../graph-layout/validate.js";
import { siteAssetVersion } from "./assets.js";
import { attr, esc } from "./graph-escape.js";
import { createGraphMeasurer, GraphMeasurementUnavailableError,
  type GraphMeasurerOptions, type GraphMeasurementEnvironment, type GraphMeasurementStatistics } from "./graph-measure.js";
import { measureDisplayGraph, projectGraph, type DisplayGraph, type FlatGraphInput,
  type GraphKind, type GraphLabel, type MeasuredDisplayGraph, type ProofGraphData } from "./graph-project.js";
import { graphInteractionPayload, graphSvg, type GraphInteractionPayload } from "./graph-svg.js";
import { graphDataScript } from "./graphs.js";
import { displayLabelRequests } from "./graph-node-size.js";

export interface PreparedGraphView {
  interaction: GraphInteractionPayload; height: number; status: string;
  /** Initial SVG is already in the container; interaction retains its bytes. */
  svg?: string;
  /** A same-origin static JSON object containing SVG and interaction data. */
  src?: string;
}
export interface PreparedGraphDescriptor {
  initial: string; ancestors: number; descendants: number;
  views: Record<string, PreparedGraphView>;
}
export interface LocalGraphDescriptor {
  environment: GraphMeasurementEnvironment;
  profile: LayoutProfile;
  requests: ReturnType<typeof displayLabelRequests>;
  containers: Record<string, {
    kind: GraphKind; initial: string; ancestors: number; descendants: number;
    views: Record<string, { display: DisplayGraph; status: string }>;
  }>;
}
export interface GraphPreparationOptions {
  mode?: "archive" | "local"; cacheDir?: string; selfContained?: boolean;
  log?: (message: string) => void; measurement?: GraphMeasurerOptions;
  /** Transfer threshold only. No topology or incidence is dropped above it. */
  alternateInlineLimit?: number;
  profile?: LayoutProfile;
}
export interface GraphPreparationDiagnostic extends Diagnostic {
  page?: string; container?: string; state?: string; inputDigest?: string;
}
export interface GraphPreparationStatistics {
  pages: number; containers: number; views: number; uniqueLayouts: number;
  layoutCacheHits: number; layoutCacheMisses: number; corruptGeometryEntries: number;
  staticSvgBytes: number; alternateFiles: number; alternateBytes: number;
  measurement?: GraphMeasurementStatistics;
  phasesMs: { projection: number; measurement: number; layout: number; serialization: number; total: number };
  layouts: {
    inputDigest: string; kind: GraphKind; cache: "hit" | "miss";
    metrics: GeometryMetrics; elapsedMs: number;
    stats?: LayoutResult["stats"]; candidates?: LayoutResult["candidates"];
  }[];
}
export interface GraphPreparationResult {
  localFallback: boolean; diagnostics: GraphPreparationDiagnostic[]; statistics: GraphPreparationStatistics;
}

type PublicGraphData = Record<GraphKind, FlatGraphInput | ProofGraphData>;
type RawRecord = Record<string, unknown>;
interface View { state: string; status: string; display: DisplayGraph }
interface Container {
  id: string; kind: GraphKind; initial: string; ancestors: number; descendants: number;
  original: string; attributes: string; views: View[];
}
interface PageGraphs { file: string; html: string; rawScript: string; payload: Partial<PublicGraphData>; containers: Container[] }
interface GeometryResult { geometry: GraphGeometry; diagnostics: readonly Diagnostic[]; metrics: GeometryMetrics }

const KINDS: readonly GraphKind[] = ["concepts", "proofs", "submissions"];
const CONTAINER_IDS: Readonly<Record<string, GraphKind>> = {
  "concept-dag": "concepts", "proof-network": "proofs", "submission-dag": "submissions",
};
const PREPARATION_VERSION = "prepared-svg-1";
const hash = (value: unknown) => createHash("sha256").update(typeof value === "string" ? value : canonicalJson(value)).digest("hex");
const plural = (count: number, singular: string) => `${count} ${singular}${count === 1 ? "" : "s"}`;

function fail(code: string, message: string, ...ids: string[]): never {
  throw new GraphDiagnosticError([{ code, message, ...(ids.length ? { ids } : {}) }]);
}
function record(value: unknown, description: string): RawRecord {
  if (!value || typeof value !== "object" || Array.isArray(value)) fail("graph-presentation", `${description} must be an object`);
  return value as RawRecord;
}
function requiredString(value: unknown, description: string): string {
  if (typeof value !== "string" || !value) fail("graph-presentation", `${description} must be a nonempty string`);
  return value;
}
function list(value: unknown, description: string): unknown[] {
  if (!Array.isArray(value)) fail("graph-presentation", `${description} must be an array`);
  return value;
}
function copyFields(source: RawRecord, target: RawRecord, keys: readonly string[], type: "string" | "number" | "boolean"): void {
  for (const key of keys) if (source[key] !== undefined) {
    if (typeof source[key] !== type || (type === "number" && !Number.isFinite(source[key])))
      fail("graph-presentation", `Graph presentation field ${key} has an invalid type`);
    target[key] = source[key];
  }
}
function safeNode(value: unknown, statement: boolean): RawRecord {
  const raw = record(value, "Graph node"), node: RawRecord = { id: requiredString(raw.id, "Graph node identity") };
  copyFields(raw, node, ["title", "href", "dir", "status", "owner", "state"], "string");
  copyFields(raw, node, ["ext"], "boolean");
  copyFields(raw, node, ["concepts", "proofs"], "number");
  if (statement) {
    copyFields(raw, node, ["label", "concept", "tooltipHtml", "endpointKind"], "string");
    copyFields(raw, node, ["index", "count"], "number");
    copyFields(raw, node, ["proven"], "boolean");
  }
  if (node.dir !== undefined && !["core", "up", "down"].includes(String(node.dir))) fail("graph-direction", "Unknown graph visibility direction", String(node.id));
  if (node.status !== undefined && !["none", "open", "proven"].includes(String(node.status))) fail("graph-status", "Unknown concept status", String(node.id));
  return node;
}

function safeDetailHref(value: unknown, description: string, external = false): string {
  const href = requiredString(value, description);
  if (/[\u0000-\u001f]/u.test(href)) fail("graph-detail-link", `${description} contains control characters`);
  if (!external) {
    if (/^(?:[a-z][a-z0-9+.-]*:|\/\/)/iu.test(href))
      fail("graph-detail-link", `${description} must be a relative public page URL`);
    return href;
  }
  try {
    if (new URL(href).protocol !== "https:") throw new Error("not HTTPS");
  } catch { fail("graph-detail-link", `${description} must be an HTTPS URL`); }
  return href;
}

function safeDetailClaim(value: unknown): RawRecord {
  const raw = record(value, "Graph detail claim"), claim: RawRecord = {
    id: requiredString(raw.id, "Graph detail claim identity"),
    name: requiredString(raw.name, "Graph detail claim name"),
  };
  if (typeof raw.proven !== "boolean") fail("graph-detail", "Graph detail claim status must be boolean");
  claim.proven = raw.proven;
  if (raw.href !== undefined) claim.href = safeDetailHref(raw.href, "Graph detail claim link");
  copyFields(raw, claim, ["nameHtml"], "string");
  copyFields(raw, claim, ["statement", "statementCount"], "number");
  return claim;
}

function safeGraphDetails(value: unknown): RawRecord {
  const raw = record(value, "Proof graph details"), details: RawRecord = Object.create(null) as RawRecord;
  for (const [key, value] of Object.entries(raw).sort(([a], [b]) => compareText(a, b))) {
    const source = record(value, "Proof graph detail");
    const kind = requiredString(source.kind, "Proof graph detail kind");
    if (!["concept", "proof"].includes(kind) || !key.startsWith(`${kind}:`))
      fail("graph-detail", "Proof graph detail kind does not match its key", key);
    const detail: RawRecord = { kind, name: requiredString(source.name, "Proof graph detail name") };
    copyFields(source, detail, ["nameHtml", "type", "status", "statusDetail", "descriptionHtml", "reviewLabel", "leanPath"], "string");
    copyFields(source, detail, ["openAssumptions"], "number");
    if (source.openAssumptionIds !== undefined) {
      detail.openAssumptionIds = list(source.openAssumptionIds, "Proof graph open assumptions")
        .map((id) => requiredString(id, "Open-assumption identity")).sort(compareText);
    }
    if (source.anonymousReview !== undefined) {
      if (typeof source.anonymousReview !== "boolean") fail("graph-detail", "Proof graph anonymous-review state must be boolean");
      detail.anonymousReview = source.anonymousReview;
    }
    if (source.href !== undefined) detail.href = safeDetailHref(source.href, "Proof graph detail page link");
    if (source.reviewUrl !== undefined) detail.reviewUrl = safeDetailHref(source.reviewUrl, "Proof graph review link", true);
    if (source.sourceHref !== undefined) detail.sourceHref = safeDetailHref(source.sourceHref, "Proof graph source link", true);
    if (source.submission !== undefined) {
      const submission = record(source.submission, "Proof graph detail submission");
      const safeSubmission: RawRecord = {
        id: requiredString(submission.id, "Proof graph detail submission identity"),
        name: requiredString(submission.name, "Proof graph detail submission name"),
        state: requiredString(submission.state, "Proof graph detail submission state"),
      };
      copyFields(submission, safeSubmission, ["nameHtml"], "string");
      if (submission.href !== undefined) safeSubmission.href = safeDetailHref(submission.href, "Proof graph submission page link");
      detail.submission = safeSubmission;
    }
    if (source.statements !== undefined) detail.statements = list(source.statements, "Proof graph detail statements").map((value) => {
      const statement = record(value, "Proof graph detail statement"), out: RawRecord = {
        id: requiredString(statement.id, "Proof graph detail statement identity"),
        name: requiredString(statement.name, "Proof graph detail statement name"),
        signature: requiredString(statement.signature, "Proof graph detail Lean signature"),
      };
      if (typeof statement.proven !== "boolean") fail("graph-detail", "Proof graph detail statement status must be boolean");
      out.proven = statement.proven;
      if (statement.href !== undefined) out.href = safeDetailHref(statement.href, "Proof graph detail statement link");
      return out;
    });
    if (source.sections !== undefined) detail.sections = list(source.sections, "Proof graph detail sections").map((value) => {
      const section = record(value, "Proof graph detail section"), out: RawRecord = {};
      copyFields(section, out, ["titleHtml", "bodyHtml"], "string");
      return out;
    });
    if (source.conclusion !== undefined) detail.conclusion = safeDetailClaim(source.conclusion);
    if (source.assumptions !== undefined) detail.assumptions = list(source.assumptions, "Proof graph detail assumptions").map(safeDetailClaim);
    details[key] = detail;
  }
  return details;
}

/** No object spread of unknown input. The old raw semantic payload remains
 * available to readers/tests, but source/author/private extras are excluded. */
export function publicGraphPayload(input: unknown): Partial<PublicGraphData> {
  const raw = record(input, "Graph data"), result: Partial<PublicGraphData> = {};
  for (const kind of KINDS) if (raw[kind] !== undefined && raw[kind] !== null) {
    const data = record(raw[kind], `${kind} data`), safe: RawRecord = {};
    copyFields(data, safe, ["home"], "string");
    if (kind === "proofs") {
      safe.statements = list(data.statements, "Proof statements").map((node) => safeNode(node, true))
        .sort((a, b) => compareText(String(a.id), String(b.id)));
      safe.proofs = list(data.proofs, "Proof incidences").map((value) => {
        const proof = record(value, "Proof"), out: RawRecord = {
          id: requiredString(proof.id, "Proof identity"), conclusion: requiredString(proof.conclusion, "Proof conclusion"),
          assumptions: list(proof.assumptions, "Proof assumptions").map((id) => requiredString(id, "Assumption identity")).sort(compareText),
        };
        copyFields(proof, out, ["description", "tooltipHtml", "href", "owner"], "string");
        copyFields(proof, out, ["ext", "assumptionsProven"], "boolean");
        copyFields(proof, out, ["outstanding"], "number");
        return out;
      }).sort((a, b) => compareText(String(a.id), String(b.id)));
      if (data.details !== undefined) safe.details = safeGraphDetails(data.details);
    } else {
      safe.nodes = list(data.nodes, "Graph nodes").map((node) => safeNode(node, false))
        .sort((a, b) => compareText(String(a.id), String(b.id)));
      safe.edges = list(data.edges, "Graph edges").map((value) => {
        const edge = record(value, "Edge"), out: RawRecord = {
          from: requiredString(edge.from, "Edge source"), to: requiredString(edge.to, "Edge target"),
        };
        copyFields(edge, out, ["id", "kind"], "string");
        return out;
      }).sort((a, b) => compareText(canonicalJson(a), canonicalJson(b)));
    }
    result[kind] = safe as unknown as FlatGraphInput | ProofGraphData;
  }
  return deepFreeze(result);
}

function attribute(attributes: string, name: string): string | undefined {
  return new RegExp(`(?:^|\\s)${name}\\s*=\\s*(["'])(.*?)\\1`, "u").exec(attributes)?.[2];
}
function pagePrefix(file: string): string {
  return "../".repeat(Math.max(0, file.replace(/\\/gu, "/").split("/").length - 1));
}
function conceptStatus(state: string, count: number, up: number, down: number): string {
  const parts = [plural(count, "concept")];
  if (state[0] === "0" && up) parts.push(`${plural(up, "ancestor")} hidden`);
  if (state[1] === "0" && down) parts.push(`${plural(down, "descendant")} hidden`);
  return parts.join("; ");
}

function scanPages(files: ReadonlyMap<string, string | Buffer>): PageGraphs[] {
  const pages: PageGraphs[] = [];
  for (const [file, content] of [...files].sort(([a], [b]) => compareText(a, b))) {
    if (!file.endsWith(".html")) continue;
    const html = typeof content === "string" ? content : content.toString("utf8");
    const scripts = [...html.matchAll(/<script\b[^>]*\bid=["']graph-data["'][^>]*>([\s\S]*?)<\/script>/gu)];
    if (!scripts.length) continue;
    if (scripts.length > 1) fail("duplicate-graph-data", "A page must contain one graph payload", file);
    const script = scripts[0]!;
    let parsed: unknown;
    try { parsed = JSON.parse(script[1]!); }
    catch { fail("graph-json", "Graph presentation JSON is invalid", file); }
    const payload = publicGraphPayload(parsed), containers: Container[] = [];
    // Validate the full semantic graph before intentional view filtering can
    // remove either endpoint. Missing declarations must never disappear here.
    for (const kind of KINDS) if (payload[kind]) projectGraph(kind, payload[kind]!);
    const ids = new Set<string>();
    for (const match of html.matchAll(/<div\b([^>]*\bid=["'](?:concept-dag|proof-network|submission-dag)["'][^>]*)>[\s\S]*?<\/div>/gu)) {
      const attributes = match[1]!, id = attribute(attributes, "id")!, kind = CONTAINER_IDS[id]!;
      if (ids.has(id)) fail("duplicate-graph-container", "A graph container identity occurs twice on one page", file, id);
      ids.add(id);
      const data = payload[kind];
      if (!data) fail("missing-graph-data", "A graph container has no semantic payload", file, id);
      let initial = "default", ancestors = 0, descendants = 0;
      const views: View[] = [];
      if (kind === "concepts") {
        const flat = data as FlatGraphInput;
        ancestors = flat.nodes.filter((node) => node.dir === "up").length;
        descendants = flat.nodes.filter((node) => node.dir === "down").length;
        initial = `${ancestors && attribute(attributes, "data-ancestry") === "true" ? "1" : "0"}${descendants && attribute(attributes, "data-descendants") === "true" ? "1" : "0"}`;
        for (const up of ancestors ? ["0", "1"] : ["0"]) for (const down of descendants ? ["0", "1"] : ["0"]) {
          const state = up + down;
          const nodes = flat.nodes.filter((node) => (node.dir ?? "core") === "core" ||
            (node.dir === "up" ? up === "1" : down === "1"));
          const visible = new Set(nodes.map((node) => node.id));
          const filtered = { nodes, edges: flat.edges.filter((edge) => visible.has(edge.from) && visible.has(edge.to)) };
          views.push({ state, status: conceptStatus(state, nodes.length, ancestors, descendants), display: projectGraph(kind, filtered) });
        }
      } else views.push({ state: initial, status: kind === "proofs"
        ? `${plural((data as ProofGraphData).statements.length, "statement")}; ${plural((data as ProofGraphData).proofs.length, "proof")}`
        : plural((data as FlatGraphInput).nodes.length, "submission"), display: projectGraph(kind, data) });
      containers.push({ id, kind, initial, ancestors, descendants, attributes, original: match[0], views });
    }
    pages.push({ file, html, rawScript: script[0], payload, containers });
  }
  return pages;
}

function updateCsp(html: string, directive: string, source: string): string {
  return html.replace(/(<meta\b[^>]*http-equiv="Content-Security-Policy"[^>]*content=")([^"]*)(")/u, (_all, before, policy: string, after) => {
    const clauses = policy.split(";").map((part) => part.trim()).filter(Boolean);
    const index = clauses.findIndex((part) => part.split(/\s/u)[0] === directive);
    if (index < 0) clauses.push(`${directive} ${source}`);
    else if (!clauses[index]!.split(/\s+/u).includes(source)) clauses[index] += ` ${source}`;
    return before + clauses.join("; ") + after;
  });
}
function installScript(html: string, file: string, asset: string): string {
  const escaped = asset.replace(/[.*+?^${}()|[\]\\]/gu, "\\$&");
  if (new RegExp(`<script\\b[^>]*\\bsrc=["'][^"']*assets/${escaped}(?:\\?[^"']*)?["']`, "u").test(html)) return html;
  const tag = `<script src="${attr(pagePrefix(file) + "assets/" + asset)}?v=${siteAssetVersion(asset)}"></script>`;
  return html.includes("</body>") ? html.replace("</body>", `${tag}\n</body>`) : `${html}\n${tag}`;
}
function installInteraction(html: string, file: string): string {
  const withoutLegacy = html.replace(/<script\b[^>]*\bsrc=["'][^"']*assets\/(?:layout|dag)\.js(?:\?[^"']*)?["'][^>]*>\s*<\/script>\s*/gu, "");
  return updateCsp(installScript(withoutLegacy, file, "graph-interaction.js"), "connect-src", "'self'");
}
function preparedContainer(container: Container, svg: string, height: number): string {
  let attributes = container.attributes.replace(/\sstyle=(["'])[\s\S]*?\1/gu, "");
  attributes = attributes.replace(/\sdata-prepared(?:=(["']).*?\1)?/gu, "");
  return `<div${attributes} data-prepared="true" style="height:${Math.max(48, Math.min(720, height))}px">${svg}</div>`;
}
function initialConceptControls(html: string, container: Container): string {
  const view = container.views.find((candidate) => candidate.state === container.initial)!;
  html = html.replace(/(<output\b[^>]*\bid="concept-graph-status"[^>]*>)[\s\S]*?(<\/output>)/u, `$1${esc(view.status)}$2`);
  for (const [id, index, name, count] of [
    ["concept-expand", 0, "ancestors", container.ancestors], ["concept-descend", 1, "descendants", container.descendants],
  ] as const) {
    const on = container.initial[index] === "1";
    html = html.replace(new RegExp(`<button\\b([^>]*\\bid="${id}"[^>]*)>[\\s\\S]*?<\\/button>`, "u"), (_match, rawAttributes: string) => {
      const attributes = rawAttributes.replace(/\saria-pressed="[^"]*"/gu, "").replace(/\sdisabled(?:="[^"]*")?/gu, "");
      return `<button${attributes} disabled aria-pressed="${on && count > 0}">${count ? `${on ? "Hide" : "Show"} ${name}` : `No ${name}`}</button>`;
    });
  }
  return html;
}

function onlyKeys(value: object, keys: readonly string[]): boolean { return Object.keys(value).every((key) => keys.includes(key)); }
/** Cache hits accept only the public core geometry schema, never arbitrary
 * attributes left by a previous/private producer, even with a matching hash. */
function geometryFields(geometry: GraphGeometry): boolean {
  const point = (p: object) => onlyKeys(p, ["x", "y"]), rect = (r: object) => onlyKeys(r, ["x", "y", "width", "height"]);
  return onlyKeys(geometry, ["schemaVersion", "engineVersion", "profileId", "inputDigest", "bounds", "nodes", "ports", "edges", "groups"]) && rect(geometry.bounds) &&
    geometry.nodes.every((node) => onlyKeys(node, ["id", "x", "y", "width", "height", "rank", "parentId"])) &&
    geometry.ports.every((port) => onlyKeys(port, ["id", "nodeId", "x", "y"])) &&
    geometry.edges.every((edge) => onlyKeys(edge, ["id", "sections"]) && edge.sections.every((section) =>
      onlyKeys(section, ["id", "points", "nextSectionIds", "terminalTargetPortId", "role", "commands"]) && section.points.every(point) &&
      (!section.commands || section.commands.every((command) => onlyKeys(command, command.kind === "Q" ? ["kind", "p", "control"] : ["kind", "p"]) &&
        point(command.p) && (command.kind !== "Q" || point(command.control)))))) &&
    (!geometry.groups || geometry.groups.every((group) => onlyKeys(group, ["id", "x", "y", "width", "height", "memberIds", "labelBoxes", "gates"]) && group.labelBoxes.every(rect) &&
      (!group.gates || group.gates.every((gate) => onlyKeys(gate, ["id", "edgeId", "side", "point"]) && point(gate.point)))));
}
function writeAtomic(file: string, value: unknown): void {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.${randomUUID()}.tmp`;
  try { fs.writeFileSync(temporary, canonicalJson(value) + "\n"); fs.renameSync(temporary, file); }
  finally { if (fs.existsSync(temporary)) fs.unlinkSync(temporary); }
}

/** Only the typed layout settings cross the local worker boundary. A host
 * profile can carry unrelated/private metadata that must stay on the host. */
function localProfile(profile: LayoutProfile): LayoutProfile {
  const result = {} as Record<keyof LayoutProfile, string | number>;
  const integerFields = new Set(["rankPivots", "sweeps", "siftingMoves", "exactLayerLimit", "dpStates", "expandedVertices", "routingExpansions", "candidates"]);
  for (const key of Object.keys(DEFAULT_PROFILE) as (keyof LayoutProfile)[]) {
    const value = profile[key];
    if (key === "id" ? typeof value !== "string" || !value.trim()
      : typeof value !== "number" || !Number.isFinite(value) || value < 0 ||
        (integerFields.has(key) && !Number.isSafeInteger(value)) || (key === "portSeparation" && value === 0))
      fail("local-graph-profile", `Invalid local graph profile field ${key}`);
    result[key] = value;
  }
  return Object.freeze(result) as LayoutProfile;
}

/** The cache key includes semantic attachment/projection and exact dimensions,
 * but excludes decoration/URLs/tooltips. Those never influence node positions. */
export function graphGeometryDigest(measured: MeasuredDisplayGraph, labelSignatures: readonly string[],
  environment: GraphMeasurementEnvironment, profile: LayoutProfile = DEFAULT_PROFILE): string {
  return hash({ preparationVersion: PREPARATION_VERSION, engineVersion: ENGINE_VERSION,
    schemaVersion: GEOMETRY_SCHEMA_VERSION, selectionPolicy: SELECTION_POLICY, profile,
    graph: measured.graph, kind: measured.display.kind, mapping: measured.display.mapping,
    labelSignatures: [...new Set(labelSignatures)].sort(compareText),
    measurementSignature: environment.signature, fontSignature: environment.fontSignature });
}

/** Mutates files only once all requested pages and views have been validated.
 * A hard error leaves the existing page map untouched for atomic publication. */
export async function prepareGraphs(files: Map<string, string | Buffer>, options: GraphPreparationOptions = {}): Promise<GraphPreparationResult> {
  const started = performance.now(), projectionStarted = performance.now();
  const pages = scanPages(files), diagnostics: GraphPreparationDiagnostic[] = [];
  const statistics: GraphPreparationStatistics = {
    pages: pages.length, containers: pages.reduce((sum, page) => sum + page.containers.length, 0),
    views: pages.reduce((sum, page) => sum + page.containers.reduce((n, container) => n + container.views.length, 0), 0),
    uniqueLayouts: 0, layoutCacheHits: 0, layoutCacheMisses: 0, corruptGeometryEntries: 0,
    staticSvgBytes: 0, alternateFiles: 0, alternateBytes: 0,
    phasesMs: { projection: performance.now() - projectionStarted, measurement: 0, layout: 0, serialization: 0, total: 0 }, layouts: [],
  };
  if (!pages.length) { statistics.phasesMs.total = performance.now() - started; return { localFallback: false, diagnostics, statistics }; }
  const pendingFiles = new Map<string, string | Buffer>(), profile = options.profile ?? DEFAULT_PROFILE;
  const inlineLimit = options.alternateInlineLimit ?? 32 * 1024;
  if (!Number.isSafeInteger(inlineLimit) || inlineLimit < 0) fail("graph-alternate-threshold", "Alternate transfer threshold must be a nonnegative integer");
  const measurer = createGraphMeasurer({ ...(options.cacheDir ? { cacheDir: path.join(options.cacheDir, "labels") } : {}), ...options.measurement });
  const requests = displayLabelRequests(pages.flatMap((page) => page.containers.flatMap((container) => container.views.map((view) => view.display))));
  const labelTexts = requests.map((request) => request.text);
  try {
    const measurementStarted = performance.now();
    let metrics: Awaited<ReturnType<typeof measurer.measureLabels>>;
    try { metrics = await measurer.measureLabels(requests); }
    catch (error) {
      if (options.mode !== "local" || !(error instanceof GraphMeasurementUnavailableError)) throw error;
      // The only browser-layout path is an explicitly local, separately
      // packaged one. No partially prepared archive view can reach files.
      const workerProfile = localProfile(profile);
      for (const page of pages) {
        const local: LocalGraphDescriptor = { environment: measurer.environment, profile: workerProfile,
          requests: displayLabelRequests(page.containers.flatMap((container) => container.views.map((view) => view.display))), containers: {} };
        let html = page.html;
        for (const container of page.containers) {
          local.containers[container.id] = { kind: container.kind, initial: container.initial,
            ancestors: container.ancestors, descendants: container.descendants,
            views: Object.fromEntries(container.views.map((view) => [view.state, { display: view.display, status: view.status }])) };
          html = html.replace(container.original, () => `<div${container.attributes} data-graph-local="true"><p class="empty-note" role="status">Preparing this local graph with the browser’s fonts…</p><noscript>Enable JavaScript to prepare newly authored local labels, or use a host with exact graph measurement.</noscript></div>`);
        }
        html = html.replace(page.rawScript, () => graphDataScript({ ...page.payload, local }));
        html = installInteraction(html, page.file);
        html = installScript(html, page.file, "graph-measure-local.js");
        html = installScript(html, page.file, "graph-local.js");
        pendingFiles.set(page.file, updateCsp(html, "worker-src", "'self'"));
      }
      diagnostics.push({ code: "local-graph-measurement", message: "New local labels use the separately packaged browser/worker path because host measurement is unavailable." });
      statistics.measurement = measurer.statistics;
      statistics.phasesMs.measurement = performance.now() - measurementStarted;
      statistics.phasesMs.total = performance.now() - started;
      for (const [file, contents] of pendingFiles) files.set(file, contents);
      return { localFallback: true, diagnostics, statistics };
    }
    statistics.phasesMs.measurement = performance.now() - measurementStarted;
    statistics.measurement = measurer.statistics;
    const labels = new Map<string, GraphLabel>(labelTexts.map((label, index) => [label, metrics[index]!]));
    const signatures = new Map(labelTexts.map((label, index) => [label, metrics[index]!.signature]));
    const layouts = new Map<string, GeometryResult>();
    const preparedViews = new Map<View, { measured: MeasuredDisplayGraph; geometry: GraphGeometry }>();
    const layoutStarted = performance.now();
    for (const page of pages) for (const container of page.containers) for (const view of container.views) {
      const measured = measureDisplayGraph(view.display, labels, profile.portSeparation);
      const inputDigest = graphGeometryDigest(measured, displayLabelRequests([view.display]).map((request) => signatures.get(request.text)!), measurer.environment, profile);
      let result = layouts.get(inputDigest);
      if (!result) {
        const began = performance.now();
        const cacheFile = options.cacheDir ? path.join(options.cacheDir, "geometry", `${inputDigest}.json`) : undefined;
        const reportFile = options.cacheDir ? path.join(options.cacheDir, "layout-diagnostics", `${inputDigest}.json`) : undefined;
        let algorithm: Pick<LayoutResult, "diagnostics" | "stats" | "candidates"> | undefined;
        if (cacheFile) try {
          const cached = JSON.parse(fs.readFileSync(cacheFile, "utf8")) as { schemaVersion: number; inputDigest: string; geometryDigest: string; geometry: GraphGeometry };
          if (!onlyKeys(cached, ["schemaVersion", "inputDigest", "geometryDigest", "geometry"]) || cached.schemaVersion !== 1 || cached.inputDigest !== inputDigest ||
              cached.geometryDigest !== hash(cached.geometry) || cached.geometry.inputDigest !== inputDigest ||
              cached.geometry.engineVersion !== ENGINE_VERSION || cached.geometry.profileId !== profile.id || !geometryFields(cached.geometry)) throw new Error("incompatible geometry cache");
          const checked = validateGeometry(measured.graph, cached.geometry);
          if (!checked.valid) throw new Error("invalid cached geometry");
          if (reportFile) try {
            const report = JSON.parse(fs.readFileSync(reportFile, "utf8"));
            if (report.geometryDigest === cached.geometryDigest && report.digest === hash(report.algorithm)) algorithm = report.algorithm;
          } catch { /* Performance/algorithm reports are separate optional metadata. */ }
          result = { geometry: deepFreeze(cached.geometry), metrics: checked.metrics, diagnostics: algorithm?.diagnostics ?? [] };
          statistics.layoutCacheHits++;
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== "ENOENT") statistics.corruptGeometryEntries++;
        }
        if (!result) {
          const searched = layoutGraph(measured.graph, { inputDigest, profile });
          const checked = validateGeometry(measured.graph, searched.geometry);
          if (!checked.valid || !geometryFields(searched.geometry)) throw new GraphDiagnosticError(checked.diagnostics.length ? checked.diagnostics :
            [{ code: "graph-geometry-schema", message: "Layout returned fields outside the public geometry contract" }]);
          result = { geometry: searched.geometry, diagnostics: searched.diagnostics, metrics: checked.metrics };
          algorithm = { diagnostics: searched.diagnostics, stats: searched.stats, candidates: searched.candidates };
          statistics.layoutCacheMisses++;
          if (cacheFile) writeAtomic(cacheFile, { schemaVersion: 1, inputDigest, geometryDigest: hash(result.geometry), geometry: result.geometry });
          if (reportFile) writeAtomic(reportFile, { geometryDigest: hash(result.geometry), digest: hash(algorithm), algorithm });
          statistics.layouts.push({ inputDigest, kind: container.kind, cache: "miss", metrics: result.metrics,
            elapsedMs: performance.now() - began, stats: searched.stats, candidates: searched.candidates });
        } else statistics.layouts.push({ inputDigest, kind: container.kind, cache: "hit", metrics: result.metrics,
          elapsedMs: performance.now() - began, ...(algorithm ? { stats: algorithm.stats, candidates: algorithm.candidates } : {}) });
        layouts.set(inputDigest, result);
      }
      for (const diagnostic of result.diagnostics) diagnostics.push({ ...diagnostic, inputDigest, page: page.file, container: container.id, state: view.state });
      preparedViews.set(view, { measured, geometry: result.geometry });
    }
    statistics.uniqueLayouts = layouts.size;
    statistics.phasesMs.layout = performance.now() - layoutStarted;
    const serializationStarted = performance.now();
    for (const page of pages) {
      let html = page.html;
      const prepared: Record<string, PreparedGraphDescriptor> = {};
      for (const container of page.containers) {
        const descriptor: PreparedGraphDescriptor = { initial: container.initial, ancestors: container.ancestors, descendants: container.descendants, views: {} };
        for (const view of container.views) {
          const { measured, geometry } = preparedViews.get(view)!;
          const svg = graphSvg(measured, geometry, `${container.id}-${geometry.inputDigest.slice(0, 16)}-${view.state}`);
          const complete = { svg, interaction: graphInteractionPayload(measured), height: geometry.bounds.height, status: view.status };
          if (view.state === container.initial) {
            html = html.replace(container.original, () => preparedContainer(container, svg, complete.height));
            statistics.staticSvgBytes += Buffer.byteLength(svg);
            descriptor.views[view.state] = { interaction: complete.interaction, height: complete.height, status: complete.status };
          } else {
            const bytes = canonicalJson(complete);
            if (options.selfContained || Buffer.byteLength(bytes) <= inlineLimit) descriptor.views[view.state] = complete;
            else {
              const file = `assets/graph-views/${hash(bytes)}.json`;
              if (!pendingFiles.has(file)) {
                statistics.alternateFiles++; statistics.alternateBytes += Buffer.byteLength(bytes);
                pendingFiles.set(file, bytes + "\n");
              }
              descriptor.views[view.state] = { interaction: { nodes: {}, edges: {} }, height: complete.height, status: complete.status,
                src: pagePrefix(page.file) + file };
            }
          }
        }
        prepared[container.id] = descriptor;
        if (container.kind === "concepts") html = initialConceptControls(html, container);
      }
      html = html.replace(page.rawScript, () => graphDataScript({ ...page.payload, prepared }));
      if (page.containers.length) html = installInteraction(html, page.file);
      pendingFiles.set(page.file, html);
    }
    statistics.phasesMs.serialization = performance.now() - serializationStarted;
    statistics.phasesMs.total = performance.now() - started;
    for (const [file, contents] of pendingFiles) files.set(file, contents);
    options.log?.(`Prepared ${statistics.containers} graph containers, ${statistics.views} views, ${statistics.uniqueLayouts} unique layouts (${statistics.layoutCacheHits} cached).`);
    return { localFallback: false, diagnostics, statistics };
  } finally { await measurer.close(); }
}
