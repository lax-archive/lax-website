/** The only semantic-to-display adapter. It consumes public presentation
 * payloads, never database records, repository metadata or private views. */
import { deepFreeze, compareText } from "../graph-layout/normalize.js";
import { GraphDiagnosticError, type LayoutEdge, type MeasuredGraph, type MeasuredNode, type PortSpec, type Rect } from "../graph-layout/types.js";
import { plainAuthorTitle } from "./markdown.js";

export type GraphKind = "concepts" | "submissions" | "proofs";
export interface GraphNodeInput {
  id: string; title?: string; href?: string; dir?: "core" | "up" | "down";
  status?: "proven" | "open" | "none"; ext?: boolean; owner?: string;
  state?: string; concepts?: number; proofs?: number;
}
export interface StatementGraphInput extends GraphNodeInput {
  label?: string; concept?: string; index?: number; count?: number;
  proven?: boolean; tooltipHtml?: string;
  /** Whole-concept assumptions must remain distinct from statement endpoints. */
  endpointKind?: "concept" | "statement";
}
export interface ProofGraphInput {
  id: string; assumptions: readonly string[]; conclusion: string;
  description?: string; tooltipHtml?: string; href?: string; ext?: boolean;
}
export interface FlatGraphInput {
  nodes: readonly GraphNodeInput[];
  edges: readonly { from: string; to: string; kind?: string; id?: string }[];
}
export interface ProofGraphData {
  statements: readonly StatementGraphInput[]; proofs: readonly ProofGraphInput[];
  /** Sanitized, presentation-only inspector content. It never enters layout. */
  details?: Readonly<Record<string, unknown>>;
}
export interface DisplayDock {
  id: string; statementId: string; ordinal: number; href?: string;
  status: "proven" | "open"; tooltipHtml?: string;
}
export interface DisplayNode {
  id: string; semanticId: string; kind: MeasuredNode["kind"];
  label: string; href?: string; tooltipHtml?: string;
  tooltipText?: string; tooltipRows?: readonly (readonly [string, string])[];
  status: "proven" | "open" | "none"; ext: boolean;
  docks: readonly DisplayDock[]; ports: readonly PortSpec[];
}
export interface EntityMapping {
  semanticId: string; kind: "concept" | "statement" | "proof" | "submission" | "edge" | "dock";
  nodeId?: string; portIds?: readonly string[]; edgeIds?: readonly string[];
}
export interface DisplayGraph {
  kind: GraphKind; nodes: readonly DisplayNode[]; edges: readonly LayoutEdge[];
  mapping: readonly EntityMapping[];
}
/** Exact host-measured label data needed by node sizing/serialization. */
export interface GraphLabel {
  width: number; height: number;
  lines: readonly { text: string; x: number; y: number; ink: Rect }[];
}
export interface NodeDrawing {
  body: Rect; lines: readonly { text: string; x: number; y: number; ink: Rect }[];
  docks: readonly (DisplayDock & { bounds: Rect; lines: GraphLabel["lines"] })[];
  proofRail: boolean;
}
export interface MeasuredDisplayGraph {
  display: DisplayGraph; graph: MeasuredGraph;
  drawings: ReadonlyMap<string, NodeDrawing>;
}

function diagnostic(code: string, message: string, ...ids: string[]): never {
  throw new GraphDiagnosticError([{ code, message, ids }]);
}
function title(input: string | undefined, fallback: string): string {
  return input?.trim() ? plainAuthorTitle(input).trim() || fallback : fallback;
}
/** Only generated relative page links belong here. External/source links
 * are deliberately not part of graph navigation or alternate geometry. */
function link(href: string | undefined): string | undefined {
  if (!href) return undefined;
  if (/^(?:[a-z][a-z0-9+.-]*:|\/\/)/i.test(href) || /[\u0000-\u001f]/.test(href))
    diagnostic("graph-link", "Graph navigation must be a relative public page URL");
  return href;
}

export function projectGraph(kind: GraphKind, input: FlatGraphInput | ProofGraphData): DisplayGraph {
  const nodes: (DisplayNode & { ports: PortSpec[] })[] = [];
  const edges: LayoutEdge[] = [], mapping: EntityMapping[] = [];
  const byId = new Map<string, typeof nodes[number]>();
  const endpoints = new Map<string, { nodeId: string; semanticId: string; dock?: number }>();
  const addNode = (node: typeof nodes[number]) => {
    if (byId.has(node.id)) diagnostic("duplicate-display-node", "Duplicate projected identity", node.id);
    byId.set(node.id, node); nodes.push(node);
  };
  if (kind !== "proofs") {
    const data = input as FlatGraphInput;
    for (const raw of [...data.nodes].sort((a, b) => compareText(a.id, b.id))) {
      const id = `${kind === "concepts" ? "c" : "s"}:${raw.id}`;
      const nodeKind = kind === "concepts" ? "concept" : "submission";
      const count = (n: number, noun: string) => `${n} ${noun}${n === 1 ? "" : "s"}`;
      const relations = { core: "this submission", up: "this submission builds on it", down: "it builds on this submission" };
      const tooltipRows: [string, string][] = kind === "concepts"
        ? [["Concept", title(raw.title, "Untitled concept")], ["Status", raw.status === "none" ? "definition" : raw.status ?? "unknown"],
          ...(raw.owner ? [["Submission", raw.owner] as [string, string]] : [])]
        : [["Submission", raw.id],
          ["Content", `${count(raw.concepts ?? 0, "concept")}, ${count(raw.proofs ?? 0, "proof")}`],
          ["State", raw.state ?? "unknown"], ["Relation", raw.dir ? relations[raw.dir] : "unknown"]];
      addNode({ id, semanticId: raw.id, kind: nodeKind, label: title(raw.title, raw.id), href: link(raw.href),
        tooltipRows, status: raw.status ?? "none", ext: Boolean(raw.ext), docks: [], ports: [] });
      endpoints.set(raw.id, { nodeId: id, semanticId: raw.id });
      mapping.push({ semanticId: raw.id, kind: nodeKind, nodeId: id });
    }
  } else {
    const data = input as ProofGraphData;
    const grouped = new Map<string, StatementGraphInput[]>();
    const statementIds = new Set<string>();
    for (const raw of [...data.statements].sort((a, b) => compareText(a.id, b.id))) {
      if (statementIds.has(raw.id)) diagnostic("duplicate-statement", "A statement occurs twice in the projection", raw.id);
      statementIds.add(raw.id);
      const concept = raw.concept ?? (raw.endpointKind === "concept" ? raw.id : undefined);
      const key = concept ?? raw.id;
      const members = grouped.get(key) ?? []; members.push(raw); grouped.set(key, members);
    }
    for (const [concept, members] of grouped) {
      const statementMembers = members.filter((m) => m.endpointKind !== "concept");
      const sample = statementMembers[0] ?? members[0]!;
      const multiple = (sample.count ?? 1) > 1;
      if (!multiple && statementMembers.length > 1) diagnostic("inconsistent-statement-count", "Several statements share a concept declared as single-statement", concept);
      const id = `${multiple || sample.endpointKind === "concept" ? "c" : "s"}:${multiple ? concept : sample.id}`;
      const docks: DisplayDock[] = [];
      if (multiple) {
        const count = sample.count!;
        if (statementMembers.length !== count) diagnostic("incomplete-docks", "A multi-statement concept must retain every numbered dock", concept);
        const ordinals = new Set<number>();
        for (const statement of [...statementMembers].sort((a, b) => a.index! - b.index!)) {
          if (!Number.isInteger(statement.index) || statement.index! < 1 || statement.index! > count || ordinals.has(statement.index!))
            diagnostic("dock-ordinal", "Dock ordinal is missing, duplicated or out of range; never renumber silently", statement.id);
          ordinals.add(statement.index!);
          docks.push({ id: `dock:${statement.id}`, statementId: statement.id, ordinal: statement.index!, href: link(statement.href),
            status: statement.proven ? "proven" : "open", tooltipHtml: statement.tooltipHtml });
        }
      }
      addNode({ id, semanticId: multiple ? concept : sample.id, kind: multiple || sample.endpointKind === "concept" ? "concept" : "statement",
        label: sample.label || sample.concept || sample.id, tooltipText: title(sample.title, ""),
        href: link(multiple ? sample.href?.split("#")[0] : sample.href),
        tooltipHtml: sample.tooltipHtml, status: statementMembers.length
          ? statementMembers.every((m) => m.proven) ? "proven" : "open"
          : sample.status ?? (sample.proven ? "proven" : "open"),
        ext: members.every((m) => m.ext), docks, ports: [] });
      // A concept-only endpoint is kept coarse even when siblings are known.
      endpoints.set(concept, { nodeId: id, semanticId: concept });
      mapping.push({ semanticId: concept, kind: "concept", nodeId: id });
      for (const statement of members) {
        endpoints.set(statement.id, { nodeId: id, semanticId: statement.id, ...(multiple && statement.endpointKind !== "concept" ? { dock: statement.index } : {}) });
        mapping.push({ semanticId: statement.id, kind: statement.endpointKind === "concept" ? "concept" : "statement", nodeId: id });
      }
      for (const dock of docks) mapping.push({ semanticId: dock.id, kind: "dock", nodeId: id });
    }
    for (const proof of [...data.proofs].sort((a, b) => compareText(a.id, b.id))) {
      const id = `p:${proof.id}`;
      addNode({ id, semanticId: proof.id, kind: "proof", label: "⊢", href: link(proof.href), tooltipHtml: proof.tooltipHtml,
        tooltipText: proof.description ?? "", status: "none", ext: Boolean(proof.ext), docks: [], ports: [] });
      endpoints.set(proof.id, { nodeId: id, semanticId: proof.id });
      mapping.push({ semanticId: proof.id, kind: "proof", nodeId: id });
    }
  }
  const edgeMultiplicity = new Map<string, number>();
  const addEdge = (sourceId: string, targetId: string, edgeKind: string, semanticId: string) => {
    const source = endpoints.get(sourceId), target = endpoints.get(targetId);
    if (!source || !target) diagnostic("missing-semantic-endpoint", "Display edge has no declared endpoint", semanticId, ...(!source ? [sourceId] : []), ...(!target ? [targetId] : []));
    const occurrence = edgeMultiplicity.get(semanticId) ?? 0; edgeMultiplicity.set(semanticId, occurrence + 1);
    const id = `e:${semanticId}:${occurrence}`;
    const sourcePortId = `${id}:source`, targetPortId = `${id}:target`;
    for (const [endpoint, portId, side] of [[source, sourcePortId, "north"], [target, targetPortId, "south"]] as const) {
      byId.get(endpoint.nodeId)!.ports.push({ id: portId, nodeId: endpoint.nodeId, semanticEndpointId: endpoint.semanticId,
        side, mode: endpoint.dock ? "fixed-order" : "free-on-side", ...(endpoint.dock ? { order: endpoint.dock } : {}) });
    }
    edges.push({ id, sourcePortId, targetPortId, kind: edgeKind, minRankSpan: 1, semanticIds: [semanticId] });
    mapping.push({ semanticId, kind: "edge", edgeIds: [id], portIds: [sourcePortId, targetPortId] });
  };
  if (kind === "proofs") {
    for (const proof of [...(input as ProofGraphData).proofs].sort((a, b) => compareText(a.id, b.id))) {
      for (const assumption of [...proof.assumptions].sort(compareText))
        addEdge(assumption, proof.id, "assumption", `${proof.id}:assumption:${assumption}`);
      addEdge(proof.id, proof.conclusion, "conclusion", `${proof.id}:conclusion:${proof.conclusion}`);
    }
  } else {
    for (const edge of [...(input as FlatGraphInput).edges].sort((a, b) => compareText(`${a.from}\0${a.to}\0${a.kind ?? ""}\0${a.id ?? ""}`, `${b.from}\0${b.to}\0${b.kind ?? ""}\0${b.id ?? ""}`)))
      addEdge(edge.from, edge.to, edge.kind ?? "import", edge.id ?? `${edge.from}->${edge.to}:${edge.kind ?? "import"}`);
  }
  return deepFreeze({ kind, nodes: nodes.sort((a, b) => compareText(a.id, b.id)), edges: edges.sort((a, b) => compareText(a.id, b.id)), mapping });
}

export { measureDisplayGraph } from "./graph-node-size.js";
