import { GraphDiagnosticError, type MeasuredGraph, type PortSpec } from "./types.js";

/** Unicode code-point ordering, independent of host locale and ICU version. */
export function compareText(a: string, b: string): number {
  const aa = a[Symbol.iterator](), bb = b[Symbol.iterator]();
  while (true) {
    const x = aa.next(), y = bb.next();
    if (x.done || y.done) return x.done === y.done ? 0 : x.done ? -1 : 1;
    const difference = x.value.codePointAt(0)! - y.value.codePointAt(0)!;
    if (difference) return difference;
  }
}
export function canonicalJson(value: unknown): string {
  const visit = (item: unknown): unknown => {
    if (Array.isArray(item)) return item.map(visit);
    if (item && typeof item === "object") return Object.fromEntries(Object.keys(item).sort(compareText)
      .filter((key) => (item as Record<string, unknown>)[key] !== undefined)
      .map((key) => [key, visit((item as Record<string, unknown>)[key])]));
    if (typeof item === "number" && !Number.isFinite(item)) throw new Error("nonfinite canonical number");
    return item;
  };
  return JSON.stringify(visit(value));
}
export function deepFreeze<T>(value: T): T {
  if (value && typeof value === "object" && !Object.isFrozen(value)) {
    for (const child of Object.values(value)) deepFreeze(child);
    Object.freeze(value);
  }
  return value;
}

/** Validates and copies the allowlisted core fields. Extra presentation or
 * private-view fields can never enter a layout cache through object spreads. */
export function normalizeGraph(input: MeasuredGraph): MeasuredGraph {
  const errors: { code: string; message: string; ids: string[] }[] = [];
  const fail = (code: string, message: string, ...ids: string[]) => errors.push({ code, message, ids });
  const ids = new Set<string>(), ports = new Map<string, PortSpec>(), edgeIds = new Set<string>();
  const finite = (n: number) => Number.isFinite(n) && Math.abs(n) <= 1e9;
  const nodes = input.nodes.map((node) => {
    if (!node.id || ids.has(node.id)) fail("duplicate-node", "Node identities must be unique and nonempty", node.id);
    ids.add(node.id);
    if (!finite(node.width) || !finite(node.height) || node.width <= 0 || node.height <= 0)
      fail("node-size", "Measured node size must be finite and positive", node.id);
    const labelBoxes = node.labelBoxes.map((box) => ({ x: box.x, y: box.y, width: box.width, height: box.height }));
    for (const box of [...labelBoxes, ...(node.footprints ?? []).map((f) => f.bounds)]) {
      if (![box.x, box.y, box.width, box.height].every(finite) || box.width < 0 || box.height < 0)
        fail("footprint-size", "Footprints must be finite nonnegative rectangles", node.id);
      if (box.x < -0.001 || box.y < -0.001 || box.x + box.width > node.width + 0.001 || box.y + box.height > node.height + 0.001)
        fail("footprint-outside", "Measured footprint lies outside its reserved node envelope", node.id);
    }
    const nodePorts = node.ports.map((port) => {
      if (!port.id || ports.has(port.id)) fail("duplicate-port", "Port identities must be unique and nonempty", port.id);
      if (port.nodeId !== node.id) fail("port-owner", "Port owner does not match its node", port.id, node.id);
      if (!port.semanticEndpointId) fail("port-semantic-id", "A port must name its semantic endpoint", port.id);
      if (!["north", "south", "east", "west"].includes(port.side)) fail("port-side", "Unknown port side", port.id);
      if (!["free-on-side", "free-in-slots", "fixed-order", "fixed-position"].includes(port.mode)) fail("port-mode", "Unknown port constraint", port.id);
      if ((port.mode === "fixed-position" || port.mode === "free-in-slots") && (!port.offset || !finite(port.offset.x) || !finite(port.offset.y)))
        fail("fixed-position", "A fixed port or reserved slot requires a finite node-local offset", port.id);
      if (port.mode === "fixed-order" && (!Number.isInteger(port.order) || port.order! < 0))
        fail("fixed-order", "A fixed-order port requires a nonnegative ordinal", port.id);
      if (port.offset && (port.offset.x < 0 || port.offset.y < 0 || port.offset.x > node.width || port.offset.y > node.height))
        fail("fixed-position", "Fixed port offset is outside its measured node", port.id);
      const result: PortSpec = { id: port.id, nodeId: node.id, semanticEndpointId: port.semanticEndpointId,
        side: port.side, mode: port.mode, ...(port.order === undefined ? {} : { order: port.order }),
        ...(port.offset ? { offset: { x: port.offset.x, y: port.offset.y } } : {}) };
      ports.set(port.id, result);
      return result;
    }).sort((a, b) => compareText(a.id, b.id));
    return { id: node.id, kind: node.kind, width: node.width, height: node.height, labelBoxes, ports: nodePorts,
      ...(node.footprints ? { footprints: node.footprints.map((f) => ({ id: f.id, kind: f.kind, bounds: { x: f.bounds.x, y: f.bounds.y, width: f.bounds.width, height: f.bounds.height },
        ...(f.semanticEndpointId ? { semanticEndpointId: f.semanticEndpointId } : {}) })) } : {}) };
  }).sort((a, b) => compareText(a.id, b.id));
  const edges = input.edges.map((edge) => {
    if (!edge.id || edgeIds.has(edge.id)) fail("duplicate-edge", "Edge identities must be unique and nonempty", edge.id);
    edgeIds.add(edge.id);
    for (const id of [edge.sourcePortId, edge.targetPortId]) if (!ports.has(id)) fail("missing-endpoint", "Edge names an absent port", edge.id, id);
    if (!Number.isSafeInteger(edge.minRankSpan) || edge.minRankSpan < 1) fail("minimum-span", "Minimum rank span must be a positive safe integer", edge.id);
    if (edge.weight !== undefined && (!Number.isSafeInteger(edge.weight) || edge.weight < 0)) fail("edge-weight", "Edge weight must be a nonnegative safe integer", edge.id);
    return { id: edge.id, sourcePortId: edge.sourcePortId, targetPortId: edge.targetPortId,
      kind: edge.kind, minRankSpan: edge.minRankSpan, ...(edge.weight === undefined ? {} : { weight: edge.weight }),
      ...(edge.semanticIds ? { semanticIds: [...edge.semanticIds].sort(compareText) } : {}) };
  }).sort((a, b) => compareText(a.id, b.id));
  if (errors.length) throw new GraphDiagnosticError(errors);
  return deepFreeze({ nodes, edges });
}
