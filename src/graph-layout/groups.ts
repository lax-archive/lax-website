/** Expanded displayed SCCs. Internal feedback retains semantic direction;
 * only the condensation DAG is passed to the ordinary upward layout. The
 * explicit row/lanes interior is a conservative fallback, not a claim of an
 * optimum compound drawing. */
import { condensation, indexedGraph } from "./components.js";
import { pathData, polylineCommands, quantizeGeometry, simplifyCollinear } from "./geometry.js";
import { compareText, normalizeGraph } from "./normalize.js";
import { belowBodyEscape, placePorts, portOffsets } from "./ports.js";
import { siblingInteriorFor, type Gate, type Interior } from "./sibling-groups.js";
import { DEFAULT_PROFILE, ENGINE_VERSION, GEOMETRY_SCHEMA_VERSION, GraphDiagnosticError,
  type GraphGeometry, type LayoutProfile, type MeasuredGraph, type MeasuredNode,
  type PlacedGroup, type PlacedNode, type PlacedPort, type Point,
  type PortSpec, type RouteSection } from "./types.js";
import { parsePathData, validateGeometry } from "./validate.js";

const unique = (preferred: string, occupied: Set<string>) => { let id = preferred; while (occupied.has(id)) id = ":" + id; occupied.add(id); return id; };
const move = (p: Point, shift: Point): Point => ({ x: p.x + shift.x, y: p.y + shift.y });

/** The callback contract defines a section chain by IDs, not array order. */
function inRouteOrder(sections: readonly RouteSection[]): RouteSection[] {
  const byId = new Map(sections.map((section) => [section.id, section])), referenced = new Set(sections.flatMap((section) => [...section.nextSectionIds]));
  let current = sections.find((section) => !referenced.has(section.id));
  const ordered: RouteSection[] = [], visited = new Set<string>();
  while (current && !visited.has(current.id)) {
    ordered.push(current); visited.add(current.id); current = current.nextSectionIds[0] ? byId.get(current.nextSectionIds[0]) : undefined;
  }
  if (ordered.length !== sections.length) throw new GraphDiagnosticError([{ code: "section-topology", message: "Condensation route is not a complete section chain" }]);
  return ordered;
}

function interiorFor(graph: MeasuredGraph, members: readonly number[], id: string, profile: LayoutProfile,
  scale: number, occupiedPorts: Set<string>): Interior {
  const ids = new Set(members.map((i) => graph.nodes[i]!.id)), specById = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const incidences = graph.edges.filter((edge) => ids.has(specById.get(edge.sourcePortId)!.nodeId) || ids.has(specById.get(edge.targetPortId)!.nodeId));
  const lane = Math.max(profile.portSeparation, 12) * scale, padding = Math.max(profile.clearance + 12, 24) * scale;
  const rowY = padding * 2 + lane * incidences.length;
  const rowHeight = members.reduce((height, i) => Math.max(height, graph.nodes[i]!.height), 0);
  const height = rowY + rowHeight + padding * 2 + lane * incidences.length;
  // A column belongs to exactly one incidence. This well is visibly inside
  // the containing group and distinct from every member/dock/access column.
  const wellWidth = padding * 2 + lane * incidences.length;
  const nodes: PlacedNode[] = [], access = new Map<string, number>();
  let cursor = wellWidth;
  for (const index of members) {
    const node = graph.nodes[index]!, west = node.ports.filter((p) => p.side === "west"), east = node.ports.filter((p) => p.side === "east");
    const leftRoom = padding + lane * west.length, rightRoom = padding + lane * east.length;
    const x = cursor + leftRoom;
    nodes.push({ id: node.id, parentId: id, x, y: rowY, width: node.width, height: node.height });
    west.forEach((port, i) => access.set(port.id, x - padding - i * lane));
    east.forEach((port, i) => access.set(port.id, x + node.width + padding + i * lane));
    cursor = x + node.width + rightRoom + profile.nodeGap * scale;
  }
  const width = cursor + padding, measured: MeasuredGraph = { nodes: members.map((index) => graph.nodes[index]!), edges: [] };
  const ports = placePorts(measured, nodes, portOffsets(measured, {}, profile.portSeparation)), portById = new Map(ports.map((p) => [p.id, p]));
  const routes: Interior["routes"] = new Map(), gates: Gate[] = [], outerPorts: PortSpec[] = [];
  const hemisphere = (spec: PortSpec): "north" | "south" => spec.side === "south" ? "south" : "north";
  // Endpoint-to-lane route, directed OUT from its own semantic port. Reverse
  // this list when approaching a target. The final approach is >=padding,
  // including on east/west fixed docks, and keeps the true normal direction.
  const stem = (portId: string, y: number): Point[] => {
    const p = portById.get(portId)!, spec = specById.get(portId)!;
    if (spec.side === "north") {
      const escape = belowBodyEscape(measured.nodes.find((n) => n.id === spec.nodeId)!, nodes.find((n) => n.id === spec.nodeId)!, p, profile.portSeparation);
      if (escape) return [...escape, { x: escape.at(-1)!.x, y }];
    }
    return spec.side === "east" || spec.side === "west"
      ? [p, { x: access.get(portId)!, y: p.y }, { x: access.get(portId)!, y }]
      : [p, { x: p.x, y }];
  };
  incidences.forEach((edge, ordinal) => {
    const source = specById.get(edge.sourcePortId)!, target = specById.get(edge.targetPortId)!;
    const sourceInside = ids.has(source.nodeId), targetInside = ids.has(target.nodeId);
    const top = padding + ordinal * lane, bottom = rowY + rowHeight + padding + ordinal * lane, column = padding + ordinal * lane;
    if (sourceInside && targetInside) {
      const sourcePoint = portById.get(source.id)!, targetPoint = portById.get(target.id)!;
      if (sourcePoint.x === targetPoint.x && sourcePoint.y === targetPoint.y && source.side === target.side)
        throw new GraphDiagnosticError([{ code: "scc-coincident-terminal", message: "A self-loop requires distinct visible incidence attachments to preserve both terminal normals without retracing itself", ids: [edge.id, source.id, target.id] }]);
      const aSide = hemisphere(source), bSide = hemisphere(target), a = stem(source.id, aSide === "north" ? top : bottom), b = stem(target.id, bSide === "north" ? top : bottom);
      const start = a.at(-1)!, finish = b.at(-1)!;
      const middle = aSide === bSide ? [] : [{ x: column, y: start.y }, { x: column, y: finish.y }];
      routes.set(edge.id, { role: "feedback", points: simplifyCollinear([...a, ...middle, ...b.reverse()]) });
    } else {
      const inside = sourceInside ? source : target, side = sourceInside ? "north" : "south";
      const gateId = unique(`layout:gate:${JSON.stringify([id, edge.id, side])}`, occupiedPorts);
      const point = { x: column, y: side === "north" ? 0 : height };
      gates.push({ id: gateId, edgeId: edge.id, side, point });
      outerPorts.push({ id: gateId, nodeId: id, semanticEndpointId: inside.semanticEndpointId, side, mode: "fixed-position", offset: point });
      const aSide = hemisphere(inside), path = stem(inside.id, aSide === "north" ? top : bottom), last = path.at(-1)!;
      const out = simplifyCollinear([...path, { x: column, y: last.y }, point]);
      routes.set(edge.id, { role: "group-adapter", points: sourceInside ? out : out.reverse() });
    }
  });
  return { id, kind: "cycle", width, height, members, nodes, ports, gates, routes,
    supernode: { id, kind: "scc", width, height, labelBoxes: [], ports: outerPorts } };
}

function finalGeometry(graph: MeasuredGraph, geometry: GraphGeometry): GraphGeometry {
  const quantized = quantizeGeometry(geometry);
  // Parse the exact serialized path language back before validation. Never
  // validate a high-precision intermediate while publishing a different path.
  const serialized: GraphGeometry = { ...quantized, edges: quantized.edges.map((edge) => ({ ...edge,
    sections: edge.sections.map((section) => ({ ...section, commands: parsePathData(pathData(section.commands ?? polylineCommands(section.points))) })) })) };
  const validation = validateGeometry(graph, serialized);
  if (!validation.valid) throw new GraphDiagnosticError(validation.diagnostics);
  return serialized;
}

/** Root orchestration calls this once per weak component. No layout engine is
 * imported here: the caller supplies a validated deterministic DAG layout.
 * A fixed enlargement schedule rebuilds the COMPLETE outer graph; an invalid
 * candidate is never rescued by moving members independently of routes. */
export function layoutGroups(graph: MeasuredGraph, layoutDag: (outer: MeasuredGraph) => GraphGeometry,
  inputDigest: string, profile: LayoutProfile = DEFAULT_PROFILE): GraphGeometry {
  const indexed = indexedGraph(graph), condensed = condensation(indexed.nodeCount, indexed.edges);
  const cyclic = condensed.components.map((members, component) => members.length > 1 || condensed.internalEdges[component]!.length > 0);
  if (!cyclic.some(Boolean)) return finalGeometry(graph, { ...layoutDag(graph), inputDigest });
  const sourcePorts = new Map(graph.nodes.flatMap((node) => node.ports.map((port) => [port.id, port] as const)));
  const nodeIndex = new Map(graph.nodes.map((node, i) => [node.id, i]));
  const groupIds = new Map<number, string>(), occupiedNodes = new Set(graph.nodes.map((n) => n.id));
  condensed.components.forEach((members, component) => {
    if (cyclic[component]) groupIds.set(component, unique(`layout:scc:${JSON.stringify(members.map((index) => graph.nodes[index]!.id))}`, occupiedNodes));
  });
  const groupOfPort = (portId: string) => groupIds.get(condensed.componentOf[nodeIndex.get(sourcePorts.get(portId)!.nodeId)!]!);
  let lastError: GraphDiagnosticError | undefined;
  // The local sibling-proof drawing is tried first; the generic envelope
  // schedule follows for every group it does not fit.
  for (const { sibling, scale } of [{ sibling: true, scale: 1 }, { sibling: false, scale: 1 }, { sibling: false, scale: 2 }, { sibling: false, scale: 3 }]) {
    try {
      const occupiedPorts = new Set(sourcePorts.keys()), interiors = new Map<string, Interior>();
      condensed.components.forEach((members, component) => {
        const id = groupIds.get(component);
        if (id) interiors.set(id, (sibling ? siblingInteriorFor(graph, members, id, profile, scale, occupiedPorts) : undefined) ?? interiorFor(graph, members, id, profile, scale, occupiedPorts));
      });
      if (sibling && ![...interiors.values()].some((interior) => interior.kind === "sibling-proofs")) continue;
      const gates = new Map<string, Gate>();
      for (const interior of interiors.values()) for (const gate of interior.gates) gates.set(JSON.stringify([interior.id, gate.edgeId]), gate);
      const outer = normalizeGraph({
        nodes: [...graph.nodes.filter((_, index) => !groupIds.has(condensed.componentOf[index]!)), ...[...interiors.values()].map((group) => group.supernode)],
        edges: graph.edges.filter((edge) => !groupOfPort(edge.sourcePortId) || groupOfPort(edge.sourcePortId) !== groupOfPort(edge.targetPortId)).map((edge) => {
          const sourceGroup = groupOfPort(edge.sourcePortId), targetGroup = groupOfPort(edge.targetPortId);
          return { ...edge, sourcePortId: sourceGroup ? gates.get(JSON.stringify([sourceGroup, edge.id]))!.id : edge.sourcePortId,
            targetPortId: targetGroup ? gates.get(JSON.stringify([targetGroup, edge.id]))!.id : edge.targetPortId };
        }),
      });
      const outerGeometry = finalGeometry(outer, layoutDag(outer));
      if (outerGeometry.groups?.length) throw new GraphDiagnosticError([{ code: "nested-scc-layout", message: "The condensation layout unexpectedly returned compound groups" }]);
      const outerNodes = new Map(outerGeometry.nodes.map((node) => [node.id, node]));
      const placedGroups: PlacedGroup[] = [], nodes: PlacedNode[] = outerGeometry.nodes.filter((n) => !interiors.has(n.id));
      const ports: PlacedPort[] = outerGeometry.ports.filter((p) => !interiors.has(p.nodeId));
      const interiorSections = new Map<string, Map<string, RouteSection>>();
      for (const interior of interiors.values()) {
        const position = outerNodes.get(interior.id)!;
        placedGroups.push({ id: interior.id, kind: interior.kind, x: position.x, y: position.y, width: interior.width, height: interior.height,
          memberIds: interior.members.map((i) => graph.nodes[i]!.id), labelBoxes: [],
          gates: interior.gates.map((gate) => ({ ...gate, point: move(gate.point, position) })) });
        nodes.push(...interior.nodes.map((node) => ({ ...node, ...move(node, position), ...(position.rank === undefined ? {} : { rank: position.rank }) })));
        ports.push(...interior.ports.map((port) => ({ ...port, ...move(port, position) })));
        const sections = new Map<string, RouteSection>();
        for (const [edgeId, route] of interior.routes) sections.set(edgeId, { id: "pending", role: route.role, points: route.points.map((p) => move(p, position)), nextSectionIds: [] });
        interiorSections.set(interior.id, sections);
      }
      const outerEdges = new Map(outerGeometry.edges.map((edge) => [edge.id, edge]));
      const edges = graph.edges.map((edge) => {
        const sourceGroup = groupOfPort(edge.sourcePortId), targetGroup = groupOfPort(edge.targetPortId), sections: RouteSection[] = [];
        if (sourceGroup && sourceGroup === targetGroup) sections.push(interiorSections.get(sourceGroup)!.get(edge.id)!);
        else {
          if (sourceGroup) sections.push(interiorSections.get(sourceGroup)!.get(edge.id)!);
          sections.push(...inRouteOrder(outerEdges.get(edge.id)!.sections));
          if (targetGroup) sections.push(interiorSections.get(targetGroup)!.get(edge.id)!);
        }
        return { id: edge.id, sections: sections.map((section, i): RouteSection => ({ id: `${edge.id}:section:${i}`, points: section.points,
          ...(section.commands ? { commands: section.commands } : {}), ...(section.role ? { role: section.role } : {}),
          nextSectionIds: i + 1 < sections.length ? [`${edge.id}:section:${i + 1}`] : [],
          ...(i + 1 === sections.length ? { terminalTargetPortId: edge.targetPortId } : {}) })) };
      });
      return finalGeometry(graph, { schemaVersion: GEOMETRY_SCHEMA_VERSION, engineVersion: ENGINE_VERSION, inputDigest,
        profileId: `${profile.id}:expanded-scc-${scale}`, bounds: outerGeometry.bounds,
        nodes: nodes.sort((a, b) => compareText(a.id, b.id)), ports: ports.sort((a, b) => compareText(a.id, b.id)), edges,
        groups: placedGroups.sort((a, b) => compareText(a.id, b.id)) });
    } catch (error) {
      if (!(error instanceof GraphDiagnosticError)) throw error;
      lastError = error;
    }
  }
  throw new GraphDiagnosticError([{ code: "scc-layout-invalid", message: "Expanded display SCC failed the fixed three-envelope schedule; no partial or collapsed replacement was published" }, ...lastError!.diagnostics]);
}
