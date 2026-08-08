// Deterministic submission-page graph figures. The concept import graph and
// the submission dependency graph are acyclic and drawn by one layered
// routine. The proof hypergraph is the one that can cycle: it is made
// bipartite, condensed by strongly
// connected component, then layered; cycles therefore remain visible instead
// of being disguised by a force simulation. All figures place their layers
// with the shared Sugiyama engine in layout.js (crossing minimization plus
// coordinate relaxation); this file owns pixels, edges, and interaction.
// Plain SVG DOM throughout — no library.
(() => {
  function readData() {
    const el = document.getElementById('graph-data');
    if (!el) return null;
    try { return JSON.parse(el.textContent); } catch (_) { return null; }
  }

  function truncate(id, max) {
    return id.length > max ? id.slice(0, max - 1) + '…' : id;
  }

  /** Nodes belonging to the page's own submission drop its `<id>.` prefix:
   * the repetition is noise, and the freed width goes to the part of the
   * name that actually distinguishes. External nodes keep the full id. */
  function displayId(id, home) {
    return home && id.startsWith(home + '.') ? id.slice(home.length + 1) : id;
  }

  const CHAR_W = 6.2;
  const NODE_H = 22;
  const MAX_LABEL = 28;

  function nodeWidth(label) { return Math.round(label.length * CHAR_W) + 18; }

  const SVG_NS = 'http://www.w3.org/2000/svg';

  function svgEl(parent, name, attrs = {}) {
    const el = document.createElementNS(SVG_NS, name);
    for (const [key, value] of Object.entries(attrs)) el.setAttribute(key, String(value));
    if (parent) parent.append(el);
    return el;
  }

  function follow(node) {
    if (node.href) location.href = node.href;
  }

  function makeInteractive(el, node) {
    if (!node.href) return;
    el.setAttribute('tabindex', 0);
    el.setAttribute('role', 'link');
    el.addEventListener('click', () => follow(node));
    el.addEventListener('keydown', (event) => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        follow(node);
      }
    });
  }

  // ---- tooltips: one floating panel per graph figure ----

  function figureTooltip(container) {
    const figure = container.closest('.graph-figure');
    return figure ? figure.querySelector('.graph-tooltip') : null;
  }

  function showTooltip(container, element, rows) {
    const tooltip = figureTooltip(container);
    const figure = tooltip && tooltip.closest('.graph-figure');
    if (!tooltip || !figure) return;
    tooltip.replaceChildren();
    for (const [label, value] of rows) {
      const row = document.createElement('div');
      const heading = document.createElement('strong');
      heading.textContent = label + ': ';
      row.append(heading, document.createTextNode(value));
      tooltip.append(row);
    }
    tooltip.hidden = false;
    const figureBox = figure.getBoundingClientRect();
    const elementBox = element.getBoundingClientRect();

    // Anchor the panel to the node rather than to the pointer. Prefer above,
    // then below, then either side; every placement keeps a gap around the
    // node, including the fallback when the panel cannot fit inside the
    // figure. This also keeps the panel still while the pointer crosses the
    // node's text and rectangle.
    const inset = 8;
    const gap = 10;
    const elementLeft = elementBox.left - figureBox.left;
    const elementRight = elementBox.right - figureBox.left;
    const elementTop = elementBox.top - figureBox.top;
    const elementBottom = elementBox.bottom - figureBox.top;
    const maxLeft = Math.max(inset, figureBox.width - tooltip.offsetWidth - inset);
    let left = Math.max(inset, Math.min(
      (elementLeft + elementRight - tooltip.offsetWidth) / 2,
      maxLeft,
    ));
    const above = elementTop - tooltip.offsetHeight - gap;
    const below = elementBottom + gap;
    let top;

    if (above >= inset) {
      top = above;
    } else if (below + tooltip.offsetHeight <= figureBox.height - inset) {
      top = below;
    } else {
      const maxTop = Math.max(inset, figureBox.height - tooltip.offsetHeight - inset);
      top = Math.max(inset, Math.min(
        (elementTop + elementBottom - tooltip.offsetHeight) / 2,
        maxTop,
      ));
      const right = elementRight + gap;
      const leftOfNode = elementLeft - tooltip.offsetWidth - gap;
      if (right + tooltip.offsetWidth <= figureBox.width - inset) left = right;
      else if (leftOfNode >= inset) left = leftOfNode;
      else top = elementTop < figureBox.height / 2 ? below : above;
    }
    tooltip.style.left = left + 'px';
    tooltip.style.top = top + 'px';
  }

  function hideTooltip(container) {
    const tooltip = figureTooltip(container);
    if (tooltip) tooltip.hidden = true;
  }

  function attachTooltip(el, container, rows) {
    el.addEventListener('mouseenter', () => showTooltip(container, el, rows));
    el.addEventListener('mouseleave', () => hideTooltip(container));
    el.addEventListener('focus', () => showTooltip(container, el, rows));
    el.addEventListener('blur', () => hideTooltip(container));
  }

  function appendBoxNode(parent, node, cls, label) {
    const w = nodeWidth(label);
    const g = svgEl(parent, 'g', { class: cls + (node.ext ? ' ext' : ''), 'aria-label': node.id });
    makeInteractive(g, node);
    svgEl(g, 'rect', { x: -w / 2, y: -NODE_H / 2, width: w, height: NODE_H, rx: 4 });
    svgEl(g, 'text', { 'text-anchor': 'middle', dy: 3.5 }).textContent = label;
    return g;
  }

  function addArrowMarker(svg, id) {
    const marker = svgEl(svgEl(svg, 'defs'), 'marker', {
      id, viewBox: '0 -5 10 10', refX: 9, refY: 0,
      markerWidth: 7, markerHeight: 7, markerUnits: 'userSpaceOnUse',
      orient: 'auto', overflow: 'visible',
    });
    // The concave tail reads more lightly than a solid triangle. `orient=auto`
    // follows the tangent of the incoming path, including diagonal and cyclic
    // edges rather than assuming that every arrow arrives vertically.
    svgEl(marker, 'path', { d: 'M1,-4.25 L9,0 L1,4.25 Q3,0 1,-4.25 Z' });
  }

  // ---- edge drawing over laxLayout routes ----

  /** Horizontal port per edge end on one side of the nodes. `ends` is
   * [{ edgeIndex, nodeId, refX }]; edges sharing a node are spread across
   * the middle of its face, ordered by where they are headed, so arrowheads
   * and stems stop piling on one point. Returns Map edgeIndex -> x. */
  function portMap(ends, centerOf, widthOf) {
    const byNode = new Map();
    for (const end of ends) {
      if (!byNode.has(end.nodeId)) byNode.set(end.nodeId, []);
      byNode.get(end.nodeId).push(end);
    }
    const ports = new Map();
    for (const [nodeId, entries] of byNode) {
      entries.sort((a, b) => a.refX - b.refX || a.edgeIndex - b.edgeIndex);
      const span = Math.min(widthOf(nodeId) * 0.7, (entries.length - 1) * 14);
      entries.forEach((entry, index) => {
        const t = entries.length === 1 ? 0 : index / (entries.length - 1) - 0.5;
        ports.set(entry.edgeIndex, centerOf(nodeId) + t * span);
      });
    }
    return ports;
  }

  /** Follow the layout's sparse route with straight runs and small rounded
   * corners. This avoids the repeated S-curves that made long edges wiggle;
   * the final run also gives the marker the true incoming direction. */
  function edgePath(points) {
    let d = `M${points[0].x},${points[0].y}`;
    for (let index = 1; index < points.length - 1; index += 1) {
      const previous = points[index - 1];
      const corner = points[index];
      const next = points[index + 1];
      const incoming = Math.hypot(corner.x - previous.x, corner.y - previous.y);
      const outgoing = Math.hypot(next.x - corner.x, next.y - corner.y);
      if (!incoming || !outgoing) continue;
      const radius = Math.min(10, incoming / 3, outgoing / 3);
      const before = {
        x: corner.x + (previous.x - corner.x) * radius / incoming,
        y: corner.y + (previous.y - corner.y) * radius / incoming,
      };
      const after = {
        x: corner.x + (next.x - corner.x) * radius / outgoing,
        y: corner.y + (next.y - corner.y) * radius / outgoing,
      };
      d += ` L${before.x},${before.y} Q${corner.x},${corner.y} ${after.x},${after.y}`;
    }
    const last = points[points.length - 1];
    return `${d} L${last.x},${last.y}`;
  }

  /** Hovering or focusing a node lights up its incident edges. */
  function attachHotEdges(el, paths) {
    if (!paths || !paths.length) return;
    const set = (on) => () => { for (const path of paths) path.classList.toggle('hot', on); };
    el.addEventListener('mouseenter', set(true));
    el.addEventListener('mouseleave', set(false));
    el.addEventListener('focus', set(true));
    el.addEventListener('blur', set(false));
  }

  // ---- layered DAG figures: dependency-free nodes at the bottom ----

  /** Draw a layered DAG into `container`: layout, edge routing, boxes,
   * tooltips. `spec` carries the per-figure specifics — the arrow marker's
   * id, the SVG's accessible name, the prefix labels drop, the node class,
   * and the tooltip rows. Everything else is the same picture, laid out by
   * the shared crossing-minimizing engine in layout.js.
   *
   * Both callers pass an acyclic graph: concept imports are Lean imports,
   * and the archive admits a dependency only on a submission that already
   * exists, so neither relation can close a loop. */
  function drawDag(container, nodes, edges, spec) {
    const labelOf = new Map(nodes.map((node) => [node.id, truncate(displayId(node.id, spec.home), MAX_LABEL)]));
    const labelWidth = (id) => nodeWidth(labelOf.get(id));
    const layout = globalThis.laxLayout.layoutDag({
      nodes: nodes.map((node) => ({ id: node.id, width: labelWidth(node.id) })),
      edges,
    });

    const padX = 32;
    const padY = 30;
    const layerGap = 76;
    const width = Math.max(container.clientWidth, Math.ceil(layout.width) + 2 * padX);
    const offsetX = (width - layout.width) / 2;
    const height = layout.maxLayer * layerGap + 2 * padY + NODE_H;
    container.style.height = Math.min(height, 680) + 'px';
    const layerY = (layer) => height - padY - NODE_H / 2 - layer * layerGap;
    const svg = svgEl(container, 'svg', {
      width, height, viewBox: `0 0 ${width} ${height}`,
      'aria-label': spec.ariaLabel,
    });
    addArrowMarker(svg, spec.arrowId);

    const positions = new Map(nodes.map((node) => {
      const p = layout.positions.get(node.id);
      return [node.id, { x: offsetX + p.x, y: layerY(p.layer) }];
    }));
    const routes = layout.routes.map((route) =>
      route.map((p) => ({ x: offsetX + p.x, y: layerY(p.layer) })));

    const sourcePorts = portMap(
      edges.map((edge, edgeIndex) => ({ edgeIndex, nodeId: edge.from,
        refX: (routes[edgeIndex][0] || positions.get(edge.to)).x })),
      (id) => positions.get(id).x, labelWidth);
    const targetPorts = portMap(
      edges.map((edge, edgeIndex) => ({ edgeIndex, nodeId: edge.to,
        refX: (routes[edgeIndex][routes[edgeIndex].length - 1] || positions.get(edge.from)).x })),
      (id) => positions.get(id).x, labelWidth);

    const group = svgEl(svg, 'g');
    const incident = new Map(nodes.map((node) => [node.id, []]));
    edges.forEach((edge, edgeIndex) => {
      const source = positions.get(edge.from);
      const target = positions.get(edge.to);
      const points = [
        { x: sourcePorts.get(edgeIndex), y: source.y - NODE_H / 2 },
        ...routes[edgeIndex],
        { x: targetPorts.get(edgeIndex), y: target.y + NODE_H / 2 },
      ];
      const path = svgEl(group, 'path', {
        class: 'dag-edge', d: edgePath(points), 'marker-end': `url(#${spec.arrowId})`,
      });
      incident.get(edge.from).push(path);
      incident.get(edge.to).push(path);
    });
    for (const node of nodes) {
      const position = positions.get(node.id);
      const g = appendBoxNode(group, node, spec.classOf(node), labelOf.get(node.id));
      g.setAttribute('transform', `translate(${position.x},${position.y})`);
      attachTooltip(g, container, spec.tooltipRows(node));
      attachHotEdges(g, incident.get(node.id));
    }
  }

  function renderConceptDag(data) {
    const container = document.getElementById('concept-dag');
    if (!container || !data || !data.nodes.length) return;
    container.replaceChildren();

    const showAncestry = container.dataset.ancestry === 'true';
    const showDescendants = container.dataset.descendants === 'true';
    const upTotal = data.nodes.filter((node) => node.dir === 'up').length;
    const downTotal = data.nodes.filter((node) => node.dir === 'down').length;
    const nodes = data.nodes.filter((node) =>
      node.dir === 'core' || (node.dir === 'up' ? showAncestry : showDescendants));
    const ids = new Set(nodes.map((node) => node.id));
    const edges = data.edges.filter((edge) => ids.has(edge.from) && ids.has(edge.to));

    const toggle = (id, total, texts, key, on) => {
      const button = document.getElementById(id);
      if (!button) return;
      button.disabled = total === 0;
      button.textContent = total === 0 ? texts.none : on ? texts.hide : texts.show;
      button.setAttribute('aria-pressed', String(on && total > 0));
      button.onclick = () => {
        container.dataset[key] = String(!on);
        renderConceptDag(data);
      };
    };
    toggle('concept-expand', upTotal,
      { none: 'No ancestors', show: 'Show ancestors', hide: 'Hide ancestors' },
      'ancestry', showAncestry);
    toggle('concept-descend', downTotal,
      { none: 'No descendants', show: 'Show descendants', hide: 'Hide descendants' },
      'descendants', showDescendants);

    const status = document.getElementById('concept-graph-status');
    if (status) {
      const parts = [`${nodes.length} concept${nodes.length === 1 ? '' : 's'}`];
      if (!showAncestry && upTotal > 0) parts.push(`${upTotal} ancestor${upTotal === 1 ? '' : 's'} hidden`);
      if (!showDescendants && downTotal > 0) parts.push(`${downTotal} descendant${downTotal === 1 ? '' : 's'} hidden`);
      status.textContent = parts.join('; ');
    }

    drawDag(container, nodes, edges, {
      home: data.home,
      arrowId: 'concept-arrow',
      ariaLabel: 'Concept dependency graph',
      classOf: (node) => 'dag-node ' + (node.status || ''),
      tooltipRows: (node) => [
        ['Concept', node.id],
        ...(node.title && node.title !== node.id ? [['Title', node.title]] : []),
        ['Status', node.status === 'none' ? 'definition' : node.status || 'unknown'],
        ...(node.owner ? [['Submission', node.owner]] : []),
      ],
    });
  }

  /** The submission map: the same picture one level up, with no toggles —
   * both directions are always drawn, and the archive is small enough in
   * this dimension that they fit. */
  function renderSubmissionDag(data) {
    const container = document.getElementById('submission-dag');
    if (!container || !data || !data.nodes.length) return;
    container.replaceChildren();

    const relation = {
      core: 'this submission',
      up: 'this submission builds on it',
      down: 'it builds on this submission',
    };
    drawDag(container, data.nodes, data.edges, {
      arrowId: 'submission-arrow',
      ariaLabel: 'Submission dependency graph',
      classOf: () => 'dag-node submission',
      tooltipRows: (node) => [
        ['Submission', node.id],
        ...(node.title && node.title !== node.id ? [['Title', node.title]] : []),
        ['Contents', `${node.concepts} concept${node.concepts === 1 ? '' : 's'}, ` +
          `${node.proofs} proof${node.proofs === 1 ? '' : 's'}`],
        ['State', node.state],
        ['Relation', relation[node.dir] || node.dir],
      ],
    });
  }

  // ---- proof network: SCC condensation laid out foundations to conclusions ----

  function stronglyConnectedComponents(nodes, adjacency) {
    let nextIndex = 0;
    const indices = new Map();
    const low = new Map();
    const stack = [];
    const onStack = new Set();
    const result = [];

    function visit(key) {
      indices.set(key, nextIndex);
      low.set(key, nextIndex);
      nextIndex += 1;
      stack.push(key);
      onStack.add(key);
      for (const target of adjacency.get(key) || []) {
        if (!indices.has(target)) {
          visit(target);
          low.set(key, Math.min(low.get(key), low.get(target)));
        } else if (onStack.has(target)) {
          low.set(key, Math.min(low.get(key), indices.get(target)));
        }
      }
      if (low.get(key) !== indices.get(key)) return;
      const component = [];
      let member;
      do {
        member = stack.pop();
        onStack.delete(member);
        component.push(member);
      } while (member !== key);
      component.sort();
      result.push(component);
    }

    [...nodes].sort().forEach((key) => { if (!indices.has(key)) visit(key); });
    return result;
  }

  function proofTooltipRows(node) {
    return [
      ['Proof', node.id],
      ...(node.description ? [['Description', node.description]] : []),
      ['Conclusion', node.conclusion],
      ['Assumptions', node.assumptions.length ? node.assumptions.join(', ') : 'none'],
      ['Submission', node.owner],
      ['Status', node.assumptionsProven ? 'grounded — all assumptions proven' : `conditional — ${node.outstanding} open assumption${node.outstanding === 1 ? '' : 's'}`],
    ];
  }

  function statementTooltipRows(node) {
    return [
      ['Claim', node.label || node.id],
      ...(node.title && node.title !== (node.label || node.id) ? [['Title', node.title]] : []),
      ...(node.label && node.label !== node.id ? [['Statement', node.id]] : []),
      ['Status', node.proven ? 'proven' : 'open'],
      ...(node.owner ? [['Submission', node.owner]] : []),
    ];
  }

  function renderProofNetwork(data) {
    const container = document.getElementById('proof-network');
    if (!container || !data || !data.proofs.length) return;
    container.replaceChildren();

    const nodes = [];
    const byKey = new Map();
    for (const statement of data.statements) {
      // One-statement rule: a claim displays as its home concept.
      const label = truncate(displayId(statement.label || statement.id, data.home), MAX_LABEL);
      const node = {
        ...statement, kind: 'statement', key: 's:' + statement.id, label,
        width: nodeWidth(label), height: NODE_H,
      };
      nodes.push(node);
      byKey.set(node.key, node);
    }
    for (const proof of data.proofs) {
      const node = { ...proof, kind: 'proof', key: 'p:' + proof.id, width: 28, height: 28 };
      nodes.push(node);
      byKey.set(node.key, node);
    }

    const links = [];
    for (const proof of data.proofs) {
      const proofKey = 'p:' + proof.id;
      for (const assumption of proof.assumptions) {
        const statementKey = 's:' + assumption;
        if (byKey.has(statementKey)) links.push({ source: statementKey, target: proofKey, kind: 'assumption' });
      }
      const conclusionKey = 's:' + proof.conclusion;
      if (byKey.has(conclusionKey)) links.push({ source: proofKey, target: conclusionKey, kind: 'conclusion' });
    }
    links.sort((a, b) => `${a.source}\0${a.target}`.localeCompare(`${b.source}\0${b.target}`));

    const adjacency = new Map(nodes.map((node) => [node.key, []]));
    for (const link of links) adjacency.get(link.source).push(link.target);
    for (const values of adjacency.values()) values.sort();
    const memberLists = stronglyConnectedComponents(adjacency.keys(), adjacency);
    const components = memberLists.map((members, id) => ({
      id,
      members,
      sortKey: members.join('\0'),
      cyclic: members.length > 1 || links.some((link) => link.source === members[0] && link.target === members[0]),
      incoming: new Set(),
      outgoing: new Set(),
    }));
    const componentOf = new Map();
    for (const component of components) for (const key of component.members) componentOf.set(key, component);
    for (const link of links) {
      const source = componentOf.get(link.source);
      const target = componentOf.get(link.target);
      if (source === target) continue;
      source.outgoing.add(target.id);
      target.incoming.add(source.id);
    }

    // Size each SCC. Cyclic components get a padded grid and enclosure;
    // singleton components are exactly their node's bounding box.
    for (const component of components) {
      const members = component.members.map((key) => byKey.get(key));
      if (!component.cyclic) {
        component.width = members[0].width;
        component.height = members[0].height;
        members[0].localX = 0;
        members[0].localY = 0;
        continue;
      }
      const columns = Math.ceil(Math.sqrt(members.length));
      const rows = Math.ceil(members.length / columns);
      const columnWidths = Array(columns).fill(0);
      const rowHeights = Array(rows).fill(0);
      members.forEach((node, index) => {
        columnWidths[index % columns] = Math.max(columnWidths[index % columns], node.width);
        rowHeights[Math.floor(index / columns)] = Math.max(rowHeights[Math.floor(index / columns)], node.height);
      });
      const contentWidth = columnWidths.reduce((sum, value) => sum + value, 0) + (columns - 1) * 24;
      const contentHeight = rowHeights.reduce((sum, value) => sum + value, 0) + (rows - 1) * 18;
      const columnCenters = [];
      const rowCenters = [];
      let cursor = -contentWidth / 2;
      for (const value of columnWidths) { columnCenters.push(cursor + value / 2); cursor += value + 24; }
      cursor = -contentHeight / 2 + 8;
      for (const value of rowHeights) { rowCenters.push(cursor + value / 2); cursor += value + 18; }
      members.forEach((node, index) => {
        node.localX = columnCenters[index % columns];
        node.localY = rowCenters[Math.floor(index / columns)];
      });
      component.width = contentWidth + 32;
      component.height = contentHeight + 48;
    }

    // Layer and place the condensation DAG with the shared engine; the
    // components are its nodes, keyed by their (unique, deterministic)
    // member list.
    const componentEdges = [];
    for (const component of components)
      for (const targetId of [...component.outgoing].sort((a, b) => a - b))
        componentEdges.push({ from: component.sortKey, to: components[targetId].sortKey });
    const layout = globalThis.laxLayout.layoutDag({
      nodes: components.map((component) => ({ id: component.sortKey, width: component.width })),
      edges: componentEdges,
      nodeGap: 44,
    });

    const rowHeights = Array(layout.maxLayer + 1).fill(0);
    for (const component of components) {
      const p = layout.positions.get(component.sortKey);
      rowHeights[p.layer] = Math.max(rowHeights[p.layer], component.height);
    }
    // A proof step (claim → turnstile → claim) spans two rows, so the gap is
    // kept small enough that one step roughly matches the concept map's 76px
    // layer rhythm instead of doubling it.
    const padX = 38;
    const padY = 26;
    const rowGap = 26;
    const width = Math.max(container.clientWidth, Math.ceil(layout.width) + 2 * padX);
    const offsetX = (width - layout.width) / 2;
    const height = rowHeights.reduce((sum, value) => sum + value, 0) + layout.maxLayer * rowGap + 2 * padY;
    container.style.height = Math.min(height, 720) + 'px';
    const layerY = [];
    let y = height - padY;
    for (let index = 0; index <= layout.maxLayer; index += 1) {
      layerY[index] = y - rowHeights[index] / 2;
      y -= rowHeights[index] + rowGap;
    }
    const svg = svgEl(container, 'svg', {
      width, height, viewBox: `0 0 ${width} ${height}`,
      'aria-label': 'Proof dependency graph',
    });
    addArrowMarker(svg, 'proof-arrow');

    for (const component of components) {
      const p = layout.positions.get(component.sortKey);
      component.x = offsetX + p.x;
      component.y = layerY[p.layer];
      for (const key of component.members) {
        const node = byKey.get(key);
        node.x = component.x + node.localX;
        node.y = component.y + node.localY;
      }
    }
    const routeOfPair = new Map();
    componentEdges.forEach((edge, index) => {
      routeOfPair.set(`${edge.from}\0${edge.to}`,
        layout.routes[index].map((p) => ({ x: offsetX + p.x, y: layerY[p.layer] })));
    });

    const group = svgEl(svg, 'g');
    for (const component of components.filter((item) => item.cyclic)) {
      svgEl(group, 'rect', {
        class: 'cycle-component',
        x: component.x - component.width / 2,
        y: component.y - component.height / 2,
        width: component.width, height: component.height, rx: 9,
      });
      svgEl(group, 'text', {
        class: 'cycle-label',
        x: component.x - component.width / 2 + 9,
        y: component.y - component.height / 2 + 14,
      }).textContent = 'cycle';
    }

    function clippedEndpoint(node, toward) {
      const dx = toward.x - node.x;
      const dy = toward.y - node.y;
      if (dx === 0 && dy === 0) return { x: node.x, y: node.y };
      const scale = 1 / Math.max(Math.abs(dx) / (node.width / 2), Math.abs(dy) / (node.height / 2));
      return { x: node.x + dx * scale, y: node.y + dy * scale };
    }

    // Cross-component links share their pair's via corridor; parallel links
    // fan out a few pixels so they stay distinguishable.
    const pairKeyOf = (link) =>
      `${componentOf.get(link.source).sortKey}\0${componentOf.get(link.target).sortKey}`;
    const pairSlots = new Map();
    links.forEach((link, index) => {
      if (componentOf.get(link.source) === componentOf.get(link.target)) return;
      const key = pairKeyOf(link);
      if (!pairSlots.has(key)) pairSlots.set(key, []);
      pairSlots.get(key).push(index);
    });
    const linkVias = links.map((link, index) => {
      if (componentOf.get(link.source) === componentOf.get(link.target)) return [];
      const siblings = pairSlots.get(pairKeyOf(link));
      const shift = (siblings.indexOf(index) - (siblings.length - 1) / 2) * 7;
      return (routeOfPair.get(pairKeyOf(link)) || []).map((p) => ({ x: p.x + shift, y: p.y }));
    });
    const crossEnds = (pick) => links.flatMap((link, edgeIndex) => {
      if (componentOf.get(link.source) === componentOf.get(link.target)) return [];
      return [pick(link, edgeIndex)];
    });
    const sourcePorts = portMap(
      crossEnds((link, edgeIndex) => ({ edgeIndex, nodeId: link.source,
        refX: (linkVias[edgeIndex][0] || byKey.get(link.target)).x })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);
    const targetPorts = portMap(
      crossEnds((link, edgeIndex) => ({ edgeIndex, nodeId: link.target,
        refX: (linkVias[edgeIndex][linkVias[edgeIndex].length - 1] || byKey.get(link.source)).x })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);

    const incident = new Map(nodes.map((node) => [node.key, []]));
    links.forEach((link, edgeIndex) => {
      const sourceNode = byKey.get(link.source);
      const targetNode = byKey.get(link.target);
      const sameComponent = componentOf.get(link.source) === componentOf.get(link.target);
      let path;
      if (sameComponent) {
        // Within an SCC there is no single flow direction, so clip the edge
        // to the boxes geometrically and bow it sideways.
        const source = clippedEndpoint(sourceNode, targetNode);
        const target = clippedEndpoint(targetNode, sourceNode);
        const bend = link.source.localeCompare(link.target) < 0 ? 14 : -14;
        const midX = (source.x + target.x) / 2;
        const midY = (source.y + target.y) / 2;
        const dx = target.x - source.x;
        const dy = target.y - source.y;
        const length = Math.hypot(dx, dy) || 1;
        const controlX = midX - dy / length * bend;
        const controlY = midY + dx / length * bend;
        path = `M${source.x},${source.y} Q${controlX},${controlY} ${target.x},${target.y}`;
      } else {
        // Condensation edges always flow upward through fixed vertical ports.
        const points = [
          { x: sourcePorts.get(edgeIndex), y: sourceNode.y - sourceNode.height / 2 },
          ...linkVias[edgeIndex],
          { x: targetPorts.get(edgeIndex), y: targetNode.y + targetNode.height / 2 },
        ];
        path = edgePath(points);
      }
      const element = svgEl(group, 'path', {
        class: `net-edge ${link.kind}`, d: path, 'marker-end': 'url(#proof-arrow)',
      });
      incident.get(link.source).push(element);
      incident.get(link.target).push(element);
    });

    for (const node of nodes) {
      if (node.kind === 'statement') {
        const g = appendBoxNode(group, node, 'net-node ' + (node.proven ? 'proven' : 'open'), node.label);
        g.setAttribute('transform', `translate(${node.x},${node.y})`);
        attachTooltip(g, container, statementTooltipRows(node));
        attachHotEdges(g, incident.get(node.key));
        continue;
      }
      const g = svgEl(group, 'g', {
        class: 'net-proof' + (node.ext ? ' ext' : ''),
        'aria-label': node.id,
        transform: `translate(${node.x},${node.y})`,
      });
      makeInteractive(g, node);
      svgEl(g, 'rect', {
        x: -node.width / 2, y: -node.height / 2,
        width: node.width, height: node.height, rx: 4,
      });
      svgEl(g, 'text', { 'text-anchor': 'middle', dy: 4.5 }).textContent = '⊢';
      attachTooltip(g, container, proofTooltipRows(node));
      attachHotEdges(g, incident.get(node.key));
    }
  }

  function render() {
    if (!globalThis.laxLayout) return;
    const data = readData();
    if (!data) return;
    renderConceptDag(data.concepts);
    renderProofNetwork(data.proofs);
    renderSubmissionDag(data.submissions);
  }

  // ---- large graph window ----

  let expandedFigure = null;

  function setGraphExpanded(button, expanded) {
    const figure = button.closest('.graph-figure');
    if (!figure) return;
    const label = button.dataset.graphLabel || 'graph';
    figure.classList.toggle('graph-expanded', expanded);
    button.setAttribute('aria-expanded', String(expanded));
    button.setAttribute('aria-label', expanded
      ? `Close ${label} large window`
      : `Open ${label} in a large window`);
    button.title = expanded ? 'Close large window' : 'Open in large window';
    if (expanded) {
      expandedFigure = figure;
      figure.setAttribute('role', 'dialog');
      figure.setAttribute('aria-modal', 'true');
      figure.setAttribute('aria-label', `${label} large view`);
    } else {
      expandedFigure = null;
      figure.removeAttribute('role');
      figure.removeAttribute('aria-modal');
      figure.removeAttribute('aria-label');
    }
    document.body.classList.toggle('graph-window-open', Boolean(expandedFigure));
    const tooltip = figure.querySelector('.graph-tooltip');
    if (tooltip) tooltip.hidden = true;
    requestAnimationFrame(render);
  }

  function installGraphExpanders() {
    for (const button of document.querySelectorAll('[data-graph-expand]')) {
      button.addEventListener('click', () => {
        const figure = button.closest('.graph-figure');
        setGraphExpanded(button, !figure.classList.contains('graph-expanded'));
      });
    }
    window.addEventListener('keydown', (event) => {
      if (event.key !== 'Escape' || !expandedFigure) return;
      event.preventDefault();
      const button = expandedFigure.querySelector('[data-graph-expand]');
      setGraphExpanded(button, false);
      button.focus();
    });
  }

  function initialize() {
    installGraphExpanders();
    render();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', initialize);
  else initialize();
  let resizeTimer;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(render, 150);
  });
})();
