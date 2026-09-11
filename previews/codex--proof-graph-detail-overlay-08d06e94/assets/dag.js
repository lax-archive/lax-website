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
  const EDGE_ROW_CLEARANCE = 10;
  const EDGE_BEND_RADIUS = 10;
  const MIN_ARC_SEPARATION = 7;
  const PROOF_NETWORK_MIN_WIDTH = 720;
  const PROOF_SELECTION_SCALE = 1.28;
  const DETAIL_PANEL_MIN_OUTSIDE_WIDTH = 320;
  const DETAIL_PANEL_MAX_OUTSIDE_WIDTH = 400;
  const DETAIL_PANEL_OUTSIDE_GAP = 16;

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

  function makeInteractive(el, node, activate = follow, role = 'link') {
    if (!activate) return;
    el.setAttribute('tabindex', 0);
    el.setAttribute('role', role);
    el.addEventListener('click', (event) => activate(node, event));
    el.addEventListener('keydown', (event) => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        activate(node, event);
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

  function appendBoxNode(parent, node, cls, label, width = node.width || nodeWidth(label), interactive = true) {
    const g = svgEl(parent, 'g', { class: cls + (node.ext ? ' ext' : ''), 'aria-label': node.id });
    if (interactive) makeInteractive(g, node, node.href ? follow : null);
    svgEl(g, 'rect', {
      x: -width / 2, y: -NODE_H / 2, width, height: NODE_H, rx: 4,
    });
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
      const span = Math.min(
        Math.max(0, widthOf(nodeId) - 2 * MIN_ARC_SEPARATION),
        (entries.length - 1) * MIN_ARC_SEPARATION,
      );
      entries.forEach((entry, index) => {
        const t = entries.length === 1 ? 0 : index / (entries.length - 1) - 0.5;
        ports.set(entry.edgeIndex, centerOf(nodeId) + t * span);
      });
    }
    return ports;
  }

  /** Render a polyline with every actual bend rounded. Duplicate and
   * collinear points disappear first, so a quadratic command is emitted for
   * every remaining corner and never for a geometrically useless one. */
  function edgePath(points) {
    const route = [];
    for (const point of points) {
      const last = route[route.length - 1];
      if (last && Math.abs(last.x - point.x) < 0.01 && Math.abs(last.y - point.y) < 0.01) continue;
      while (route.length >= 2) {
        const a = route[route.length - 2];
        const b = route[route.length - 1];
        const chord = Math.hypot(point.x - a.x, point.y - a.y);
        const twiceArea = Math.abs(
          (b.x - a.x) * (point.y - a.y) - (b.y - a.y) * (point.x - a.x));
        if (!chord || twiceArea / chord > 0.1) break;
        route.pop();
      }
      route.push(point);
    }
    if (!route.length) return '';
    let d = `M${route[0].x},${route[0].y}`;
    for (let index = 1; index + 1 < route.length; index += 1) {
      const previous = route[index - 1];
      const corner = route[index];
      const next = route[index + 1];
      const incoming = Math.hypot(corner.x - previous.x, corner.y - previous.y);
      const outgoing = Math.hypot(next.x - corner.x, next.y - corner.y);
      const radius = Math.min(EDGE_BEND_RADIUS, incoming / 2, outgoing / 2);
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
    const last = route[route.length - 1];
    return `${d} L${last.x},${last.y}`;
  }

  /** Expand a proper-layer edge chain into protected row corridors. Diagonal
   * segments live only in the empty space between ranks. At every traversed
   * rank the edge is vertical from below the tallest box to above it; at the
   * endpoints that same corridor reaches the node face. Thus an edge cannot
   * cut through an unrelated node, and its arrow always enters vertically. */
  function protectedRankRoute({ source, target, sourceX, targetX, rankVias,
    sourceLayer, targetLayer, layerCenter, layerHalfHeight }) {
    const viaByLayer = new Map(rankVias.map((point) => [point.layer, point.x]));
    const top = (layer) => layerCenter(layer) - layerHalfHeight(layer) - EDGE_ROW_CLEARANCE;
    const bottom = (layer) => layerCenter(layer) + layerHalfHeight(layer) + EDGE_ROW_CLEARANCE;
    const points = [
      { x: sourceX, y: source.y - source.height / 2 },
      { x: sourceX, y: top(sourceLayer) },
    ];
    for (let layer = sourceLayer + 1; layer < targetLayer; layer += 1) {
      const x = viaByLayer.get(layer);
      // `rankVias` is the complete dummy chain from layout.js. Refuse a
      // malformed route instead of drawing through a row whose safe slot is
      // unknown.
      if (x === undefined) throw new Error(`missing edge corridor in layer ${layer}`);
      points.push({ x, y: bottom(layer) }, { x, y: top(layer) });
    }
    points.push(
      { x: targetX, y: bottom(targetLayer) },
      { x: targetX, y: target.y + target.height / 2 },
    );
    return points;
  }

  /** Slab intersection against a padded node rectangle. End nodes are
   * excluded by the caller; every other box is treated as a hard obstacle. */
  function segmentHitsNode(first, second, node) {
    const bounds = [
      [node.x - node.width / 2 - EDGE_ROW_CLEARANCE,
        node.x + node.width / 2 + EDGE_ROW_CLEARANCE, first.x, second.x],
      [node.y - node.height / 2 - EDGE_ROW_CLEARANCE,
        node.y + node.height / 2 + EDGE_ROW_CLEARANCE, first.y, second.y],
    ];
    let lower = 0;
    let upper = 1;
    for (const [minimum, maximum, start, end] of bounds) {
      const delta = end - start;
      if (Math.abs(delta) < 1e-9) {
        if (start < minimum || start > maximum) return false;
        continue;
      }
      const firstHit = (minimum - start) / delta;
      const secondHit = (maximum - start) / delta;
      lower = Math.max(lower, Math.min(firstHit, secondHit));
      upper = Math.min(upper, Math.max(firstHit, secondHit));
      if (lower > upper) return false;
    }
    return true;
  }

  function segmentIsClear(first, second, obstacles, excluded) {
    return obstacles.every((node) => excluded.has(node.key) ||
      !segmentHitsNode(first, second, node));
  }

  /** Find the minimum-segment path through the ordered protected waypoints.
   * Segment count is primary and length breaks ties, so no retained corner
   * can be bypassed by another obstacle-free straight segment. */
  function simplifyVisibleRoute(points, obstacles, excluded) {
    const best = points.map(() => ({ segments: Infinity, length: Infinity, previous: -1 }));
    best[0] = { segments: 0, length: 0, previous: -1 };
    for (let target = 1; target < points.length; target += 1) {
      for (let source = 0; source < target; source += 1) {
        if (!Number.isFinite(best[source].segments) ||
          !segmentIsClear(points[source], points[target], obstacles, excluded)) continue;
        const segments = best[source].segments + 1;
        const length = best[source].length + Math.hypot(
          points[target].x - points[source].x,
          points[target].y - points[source].y,
        );
        if (segments < best[target].segments ||
          (segments === best[target].segments && length < best[target].length - 0.01))
          best[target] = { segments, length, previous: source };
      }
    }
    if (!Number.isFinite(best[best.length - 1].segments)) return points;
    const route = [];
    for (let index = points.length - 1; index >= 0; index = best[index].previous) {
      route.push(points[index]);
      if (index === 0) break;
    }
    return route.reverse();
  }

  /** Prefer a single straight segment. Only if a padded node rectangle blocks
   * it do we fall back to the Sugiyama rank corridors and simplify those by
   * line of sight. Arrowheads follow the final segment's actual direction. */
  function routeDagEdge(options) {
    const sourcePoint = {
      x: options.sourceX,
      y: options.source.y - options.source.height / 2,
    };
    const targetPoint = {
      x: options.targetX,
      y: options.target.y + options.target.height / 2,
    };
    const excluded = new Set([options.source.key, options.target.key]);
    if (segmentIsClear(sourcePoint, targetPoint, options.obstacles, excluded))
      return [sourcePoint, targetPoint];
    const protectedRoute = protectedRankRoute(options);
    return simplifyVisibleRoute(protectedRoute, options.obstacles, excluded);
  }

  function clippedEndpoint(node, toward) {
    const dx = toward.x - node.x;
    const dy = toward.y - node.y;
    if (dx === 0 && dy === 0) return { x: node.x, y: node.y };
    const scale = 1 / Math.max(
      Math.abs(dx) / (node.width / 2),
      Math.abs(dy) / (node.height / 2),
    );
    return { x: node.x + dx * scale, y: node.y + dy * scale };
  }

  /** A narrow surface-coloured casing separates paths where they cross. The
   * visible path is returned so node hover can still highlight it. */
  function appendEdge(parent, cls, d, markerId) {
    const route = svgEl(parent, 'g', { class: 'graph-edge-route' });
    svgEl(route, 'path', { class: 'graph-edge-hit', d });
    svgEl(route, 'path', { class: 'graph-edge-casing', d });
    return svgEl(route, 'path', {
      class: cls, d, 'marker-end': `url(#${markerId})`,
    });
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

  // ---- proof-network selection and detail drawer ----

  const proofContexts = new WeakMap();
  const reviewCache = new Map();
  let activeProofContext = null;
  let reviewSequence = 0;

  function appendText(parent, name, cls, text) {
    const element = document.createElement(name);
    if (cls) element.className = cls;
    element.textContent = text;
    parent.append(element);
    return element;
  }

  /** This markup was already rendered and sanitized by MarkdownRenderer at
   * build time. Keeping that work on the server also gives drawer formulas
   * the same KaTeX output as the concept and proof pages. */
  function appendRendered(parent, cls, html) {
    if (!html) return null;
    const element = document.createElement('div');
    element.className = cls;
    element.innerHTML = html;
    parent.append(element);
    return element;
  }

  function ensureDetailPanel(container) {
    const figure = container.closest('.graph-figure');
    if (!figure) return null;
    let panel = figure.querySelector('.graph-detail-panel');
    if (panel) return panel;
    panel = document.createElement('aside');
    panel.className = 'graph-detail-panel';
    panel.hidden = true;
    panel.setAttribute('aria-label', 'Graph details');

    const close = appendText(panel, 'button', 'graph-detail-close', '×');
    close.type = 'button';
    close.setAttribute('aria-label', 'Close graph details');
    close.addEventListener('click', () => {
      const context = proofContexts.get(container);
      const trigger = context?.trigger;
      clearProofSelection(context);
      trigger?.focus?.();
    });
    appendText(panel, 'div', 'graph-detail-scroll', '');
    figure.append(panel);
    return panel;
  }

  function detailHeading(parent, detail, eyebrow, name) {
    appendText(parent, 'p', 'graph-detail-eyebrow', eyebrow);
    const heading = document.createElement('h3');
    if (!name && detail.nameHtml) heading.innerHTML = detail.nameHtml;
    else heading.textContent = name || detail.name || 'Details';
    parent.append(heading);
    if (detail.status) {
      const status = appendText(parent, 'p', `graph-detail-status ${detail.status}`,
        detail.status + (detail.statusDetail ? ` — ${detail.statusDetail}` : ''));
      status.setAttribute('aria-label', `Status: ${status.textContent}`);
    }
  }

  function detailFacts(parent, detail) {
    const facts = [];
    if (detail.type) facts.push(['Type', detail.type]);
    if (detail.submission?.name) facts.push(['Submission', detail.submission.name]);
    if (detail.submission?.state) facts.push(['Submission state', detail.submission.state]);
    if (!facts.length) return;
    const list = document.createElement('dl');
    list.className = 'graph-detail-facts';
    for (const [term, value] of facts) {
      appendText(list, 'dt', '', term);
      appendText(list, 'dd', '', value);
    }
    parent.append(list);
  }

  function renderReviewSummary(parent, detail, panel) {
    if (!detail.reviewUrl) return;
    const section = document.createElement('section');
    section.className = 'graph-detail-review';
    appendText(section, 'h4', '', detail.reviewLabel || 'Community review');
    const values = document.createElement('div');
    values.className = 'graph-detail-review-values';
    appendText(values, 'span', 'graph-detail-review-loading', 'Loading endorsements and flags…');
    section.append(values);
    parent.append(section);

    const host = document.querySelector('[data-reactions-host]')?.dataset.reactionsHost;
    if (!host || !host.startsWith('https://')) {
      values.replaceChildren();
      appendText(values, 'span', 'graph-detail-review-unavailable', 'Review counts unavailable');
      return;
    }
    const token = String(reviewSequence += 1);
    panel.dataset.reviewToken = token;
    let request = reviewCache.get(detail.reviewUrl);
    if (!request) {
      const url = new URL('/reactions/v1/page', host);
      url.searchParams.set('url', detail.reviewUrl);
      request = fetch(url, { cache: 'no-store', headers: { Accept: 'application/json' } })
        .then((response) => {
          if (!response.ok) throw new Error(`review service returned ${response.status}`);
          return response.json();
        })
        .catch((error) => {
          reviewCache.delete(detail.reviewUrl);
          throw error;
        });
      reviewCache.set(detail.reviewUrl, request);
    }
    request.then((data) => {
      if (panel.dataset.reviewToken !== token) return;
      values.replaceChildren();
      appendText(values, 'span', 'graph-detail-review-count endorse',
        `🥳 ${Number(data.counts?.endorse) || 0} endorsement${Number(data.counts?.endorse) === 1 ? '' : 's'}`);
      appendText(values, 'span', 'graph-detail-review-count flag',
        `🚩 ${Number(data.counts?.flag) || 0} flag${Number(data.counts?.flag) === 1 ? '' : 's'}`);
    }).catch(() => {
      if (panel.dataset.reviewToken !== token) return;
      values.replaceChildren();
      appendText(values, 'span', 'graph-detail-review-unavailable', 'Review counts temporarily unavailable');
    });
  }

  function appendClaimLink(parent, claim, prefix = '') {
    const row = document.createElement('li');
    if (prefix) row.append(document.createTextNode(prefix));
    if (claim.href) {
      const link = document.createElement('a');
      link.href = claim.href;
      link.textContent = claim.name;
      row.append(link);
    } else row.append(document.createTextNode(claim.name));
    if (claim.statement) row.append(document.createTextNode(` (statement ${claim.statement} of ${claim.statementCount})`));
    row.append(document.createTextNode(claim.proven ? ' — proven' : ' — open'));
    parent.append(row);
  }

  function renderConceptDetails(parent, detail, focusStatement) {
    if (detail.descriptionHtml) {
      const section = document.createElement('section');
      appendText(section, 'h4', '', 'Natural-language statement');
      appendRendered(section, 'graph-detail-prose latex-content', detail.descriptionHtml);
      parent.append(section);
    }
    if (detail.statements?.length) {
      const section = document.createElement('section');
      appendText(section, 'h4', '', 'Lean formalization');
      for (const statement of detail.statements) {
        const block = document.createElement('div');
        block.className = 'graph-detail-formalization' +
          (focusStatement === statement.id ? ' is-focused' : '');
        if (detail.statements.length > 1)
          appendText(block, 'p', 'graph-detail-formalization-label',
            `${statement.name} · ${statement.proven ? 'proven' : 'open'}`);
        const pre = document.createElement('pre');
        appendText(pre, 'code', '', statement.signature);
        block.append(pre);
        section.append(block);
      }
      parent.append(section);
    }
  }

  function renderProofDetails(parent, detail) {
    if (detail.descriptionHtml) {
      const description = document.createElement('section');
      appendText(description, 'h4', '', 'Description');
      appendRendered(description, 'graph-detail-prose latex-content', detail.descriptionHtml);
      parent.append(description);
    }
    const section = document.createElement('section');
    appendText(section, 'h4', '', 'Checked relationship');
    const list = document.createElement('ul');
    list.className = 'graph-detail-claims';
    if (detail.assumptions?.length) {
      for (const claim of detail.assumptions) appendClaimLink(list, claim, 'Assumes ');
    } else appendText(list, 'li', '', 'No assumptions');
    if (detail.conclusion) appendClaimLink(list, detail.conclusion, 'Concludes ');
    section.append(list);
    parent.append(section);
    if (detail.leanPath) {
      const source = document.createElement('section');
      appendText(source, 'h4', '', 'Lean source');
      const code = appendText(source, 'code', 'graph-detail-path', detail.leanPath);
      if (detail.sourceHref) {
        const link = document.createElement('a');
        link.className = 'graph-detail-source-link';
        link.href = detail.sourceHref;
        link.textContent = 'View source';
        source.append(link);
      }
      code.title = detail.leanPath;
      parent.append(source);
    }
  }

  function renderDetailPanel(context, view) {
    const panel = context.panel;
    const scroll = panel.querySelector('.graph-detail-scroll');
    scroll.replaceChildren();
    const body = document.createElement('div');
    body.className = 'graph-detail-body';
    detailHeading(body, view.detail, view.eyebrow, view.name);
    if (view.relation) appendText(body, 'p', 'graph-detail-relation', view.relation);
    detailFacts(body, view.detail);
    renderReviewSummary(body, view.detail, panel);
    if (view.detail.kind === 'concept') renderConceptDetails(body, view.detail, view.focusStatement);
    else if (view.detail.kind === 'proof') renderProofDetails(body, view.detail);
    if (view.proofDetail && view.proofDetail !== view.detail) {
      const proof = document.createElement('section');
      appendText(proof, 'h4', '', 'Proof step');
      const link = document.createElement('a');
      link.href = view.proofDetail.href;
      link.textContent = view.proofDetail.name;
      proof.append(link);
      if (view.proofDetail.statusDetail)
        appendText(proof, 'p', 'graph-detail-secondary', view.proofDetail.statusDetail);
      body.append(proof);
    }
    for (const annotation of view.detail.sections || []) {
      const section = document.createElement('section');
      const heading = document.createElement('h4');
      heading.innerHTML = annotation.titleHtml;
      section.append(heading);
      appendRendered(section, 'graph-detail-prose latex-content', annotation.bodyHtml);
      body.append(section);
    }
    scroll.append(body);
    if (view.href) {
      const action = document.createElement('a');
      action.className = 'graph-detail-action';
      action.href = view.href;
      action.textContent = view.actionLabel || 'Open page';
      scroll.append(action);
    }
    panel.hidden = false;
    scroll.scrollTop = 0;
  }

  function graphClosure(context, roots) {
    const successors = new Map(context.nodes.map((node) => [node.key, []]));
    const predecessors = new Map(context.nodes.map((node) => [node.key, []]));
    for (const link of context.links) {
      successors.get(link.source)?.push(link.target);
      predecessors.get(link.target)?.push(link.source);
    }
    const related = new Set(roots);
    const visit = (adjacency, root) => {
      const pending = [root];
      while (pending.length) {
        const key = pending.pop();
        for (const next of adjacency.get(key) || []) {
          if (related.has(next)) continue;
          related.add(next);
          pending.push(next);
        }
      }
    };
    for (const root of roots) {
      visit(successors, root);
      visit(predecessors, root);
    }
    return related;
  }

  function setProofMagnification(context, magnified) {
    const scale = magnified ? PROOF_SELECTION_SCALE : 1;
    if (context.magnification === scale) return;
    context.magnification = scale;
    context.svg.style.width = `${Math.round(context.svgWidth * scale)}px`;
    context.svg.style.height = `${Math.round(context.svgHeight * scale)}px`;
    context.container.style.height = `${Math.min(
      Math.round(context.svgHeight * scale),
      720,
    )}px`;
    context.container.classList.toggle('graph-magnified', magnified);
  }

  function centerGraphSelection(context, related) {
    const boxes = [...related].flatMap((key) => {
      const node = context.byKey.get(key);
      return node ? [node] : [];
    });
    if (!boxes.length) return;
    const scale = context.magnification || 1;
    const left = Math.min(...boxes.map((node) => node.x - node.width / 2)) * scale;
    const right = Math.max(...boxes.map((node) => node.x + node.width / 2)) * scale;
    const top = Math.min(...boxes.map((node) => node.y - node.height / 2)) * scale;
    const bottom = Math.max(...boxes.map((node) => node.y + node.height / 2)) * scale;
    // The narrow-screen drawer intentionally covers the graph. It should not
    // distort the graph's scroll target as though a few pixels remained beside it.
    const measuredPanelWidth = context.panel.classList.contains('graph-detail-outside')
      ? 0
      : context.panel.offsetWidth || 0;
    const panelWidth = measuredPanelWidth < context.container.clientWidth * 0.8
      ? measuredPanelWidth : 0;
    const availableWidth = Math.max(1, context.container.clientWidth - panelWidth);
    const panelOnLeft = context.panel.classList.contains('graph-detail-left');
    const viewportCenterOffset = (panelOnLeft ? panelWidth : 0) + availableWidth / 2;
    const targetLeft = (left + right) / 2 - viewportCenterOffset;
    const targetTop = (top + bottom) / 2 - context.container.clientHeight / 2;
    context.container.scrollTo?.({
      left: Math.max(0, targetLeft),
      top: Math.max(0, targetTop),
      behavior: 'smooth',
    });
  }

  function placeDetailPanel(context) {
    const figure = context.panel.parentElement;
    const figureBox = figure.getBoundingClientRect();
    context.panel.classList.remove('graph-detail-left');
    context.panel.classList.add('graph-detail-right');

    // Keep the panel beside the graph on its right when the viewport has
    // enough room. On tighter layouts it covers the graph's right side.
    const viewportInset = 8;
    const sideSpace = document.documentElement.clientWidth - figureBox.right;
    const availableWidth = Math.floor(sideSpace - DETAIL_PANEL_OUTSIDE_GAP - viewportInset);
    const outside = availableWidth >= DETAIL_PANEL_MIN_OUTSIDE_WIDTH;
    context.panel.classList.toggle('graph-detail-outside', outside);
    if (outside) {
      context.panel.style.setProperty('--graph-detail-outside-width',
        `${Math.min(DETAIL_PANEL_MAX_OUTSIDE_WIDTH, availableWidth)}px`);
    } else {
      context.panel.style.removeProperty('--graph-detail-outside-width');
    }
  }

  function clearProofSelection(context) {
    if (!context) return;
    for (const item of context.items.values())
      item.element.classList.remove('graph-selected', 'graph-related', 'graph-dimmed');
    for (const item of context.edges)
      item.route.classList.remove('graph-selected', 'graph-related', 'graph-dimmed');
    context.selection = null;
    context.trigger = null;
    context.panel.hidden = true;
    setProofMagnification(context, false);
    delete context.panel.dataset.reviewToken;
    if (activeProofContext === context) activeProofContext = null;
  }

  function selectProofItem(context, descriptor, renderPanel = true) {
    const item = context.items.get(descriptor.token);
    if (!item) return;
    if (activeProofContext && activeProofContext !== context) clearProofSelection(activeProofContext);
    activeProofContext = context;
    context.selection = descriptor;
    context.trigger = item.element;

    const related = graphClosure(context, item.roots);
    for (const candidate of context.items.values()) {
      const isRelated = candidate.roots.some((key) => related.has(key));
      candidate.element.classList.toggle('graph-selected', candidate.token === descriptor.token);
      candidate.element.classList.toggle('graph-related', isRelated && candidate.token !== descriptor.token);
      candidate.element.classList.toggle('graph-dimmed', !isRelated);
    }
    context.edges.forEach((edge, index) => {
      const isRelated = related.has(edge.link.source) && related.has(edge.link.target);
      edge.route.classList.toggle('graph-selected', descriptor.edgeIndex === index);
      edge.route.classList.toggle('graph-related', isRelated && descriptor.edgeIndex !== index);
      edge.route.classList.toggle('graph-dimmed', !isRelated);
    });

    setProofMagnification(context, true);
    placeDetailPanel(context);
    hideTooltip(context.container);
    if (renderPanel) renderDetailPanel(context, item.view);
    requestAnimationFrame(() => centerGraphSelection(context, related));
  }

  function installProofSelection(container, data, nodes, byKey, links, nodeItems, edges) {
    const panel = ensureDetailPanel(container);
    if (!panel) return;
    const previous = proofContexts.get(container)?.selection;
    const svg = container.querySelector('svg');
    if (!svg) return;
    const context = {
      container, panel, svg, nodes, byKey, links, items: new Map(), edges,
      svgWidth: Number(svg.getAttribute('width')),
      svgHeight: Number(svg.getAttribute('height')),
      magnification: 1,
      selection: null,
      trigger: null,
    };
    proofContexts.set(container, context);

    for (const item of nodeItems) {
      const detailsKey = item.node.kind === 'proof'
        ? `proof:${item.node.id}`
        : `concept:${item.node.concept || item.node.id}`;
      const detail = data.details?.[detailsKey];
      if (!detail) continue;
      const view = {
        detail,
        eyebrow: item.node.kind === 'proof'
          ? 'Proof'
          : detail.type ? detail.type.charAt(0).toUpperCase() + detail.type.slice(1) : 'Claim',
        focusStatement: item.focusStatement,
        href: item.href || item.node.href || detail.href,
        actionLabel: item.node.kind === 'proof' ? 'Open proof page' : 'Open concept page',
      };
      const registered = { ...item, view, roots: [item.node.key] };
      context.items.set(item.token, registered);
      makeInteractive(item.element, registered,
        () => selectProofItem(context, { token: item.token }), 'button');
    }

    edges.forEach((edge, edgeIndex) => {
      const proofDetail = data.details?.[`proof:${edge.link.proofId}`];
      const statement = data.statements.find((entry) => edge.link.statementIds?.includes(entry.id));
      const conceptDetail = statement
        ? data.details?.[`concept:${statement.concept || statement.id}`]
        : null;
      if (!proofDetail || !conceptDetail) return;
      const assumption = edge.link.kind === 'assumption';
      const relation = assumption
        ? `${conceptDetail.name} is used as an assumption of ${proofDetail.name}.`
        : `${proofDetail.name} establishes ${conceptDetail.name}.`;
      const token = `edge:${edgeIndex}`;
      const hit = edge.route.querySelector('.graph-edge-hit');
      edge.route.classList.add('is-interactive');
      hit.setAttribute('aria-label', assumption
        ? `${conceptDetail.name}, assumption of ${proofDetail.name}`
        : `${proofDetail.name}, conclusion ${conceptDetail.name}`);
      const registered = {
        token,
        element: hit,
        roots: [edge.link.source, edge.link.target],
        view: {
          detail: conceptDetail,
          eyebrow: assumption ? 'Assumption link' : 'Conclusion link',
          name: conceptDetail.name,
          relation,
          proofDetail,
          focusStatement: edge.link.statementIds?.[0],
          href: proofDetail.href,
          actionLabel: 'Open proof page',
        },
      };
      context.items.set(token, registered);
      makeInteractive(hit, registered,
        () => selectProofItem(context, { token, edgeIndex }), 'button');
    });
    if (previous && context.items.has(previous.token))
      selectProofItem(context, previous);
  }

  // ---- layered DAG figures: dependency-free nodes at the bottom ----

  /** Draw a layered DAG into `container`: layout, edge routing, boxes,
   * tooltips. `spec` carries the per-figure specifics — the arrow marker's
   * id, the SVG's accessible name, the node-label rule, the node class, the
   * optional per-edge class, and the tooltip rows. Everything else is the
   * same picture, laid out by the shared crossing-minimizing engine in
   * layout.js. The arrowhead marker takes its fill from the path it ends
   * (`context-stroke` in style.css), so a recoloured edge recolours whole.
   *
   * Both callers pass an acyclic graph: concept imports are Lean imports,
   * and the archive admits a dependency only on a submission that already
   * exists, so neither relation can close a loop. */
  function drawDag(container, nodes, edges, spec) {
    const labelOf = new Map(nodes.map((node) => {
      const label = spec.labelOf ? spec.labelOf(node) : displayId(node.id, spec.home);
      return [node.id, truncate(label || node.id, MAX_LABEL)];
    }));
    const degrees = new Map(nodes.map((node) => [node.id, { incoming: 0, outgoing: 0 }]));
    for (const edge of edges) {
      degrees.get(edge.from).outgoing += 1;
      degrees.get(edge.to).incoming += 1;
    }
    const widths = new Map(nodes.map((node) => {
      const degree = degrees.get(node.id);
      const ports = Math.max(degree.incoming, degree.outgoing);
      return [node.id, Math.max(
        nodeWidth(labelOf.get(node.id)),
        (ports + 1) * MIN_ARC_SEPARATION,
      )];
    }));
    const labelWidth = (id) => widths.get(id);
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
      return [node.id, {
        x: offsetX + p.x,
        y: layerY(p.layer),
        layer: p.layer,
        height: NODE_H,
        width: labelWidth(node.id),
        key: node.id,
      }];
    }));
    const obstacles = [...positions.values()];
    const rankRoutes = layout.rankRoutes.map((route) =>
      route.map((p) => ({ x: offsetX + p.x, layer: p.layer })));

    const sourcePorts = portMap(
      edges.map((edge, edgeIndex) => ({ edgeIndex, nodeId: edge.from,
        refX: positions.get(edge.to).x })),
      (id) => positions.get(id).x, labelWidth);
    const targetPorts = portMap(
      edges.map((edge, edgeIndex) => ({ edgeIndex, nodeId: edge.to,
        refX: positions.get(edge.from).x })),
      (id) => positions.get(id).x, labelWidth);

    const group = svgEl(svg, 'g');
    const incident = new Map(nodes.map((node) => [node.id, []]));
    const pointSets = edges.map((edge, edgeIndex) => {
      const source = positions.get(edge.from);
      const target = positions.get(edge.to);
      return routeDagEdge({
        source,
        target,
        sourceX: sourcePorts.get(edgeIndex),
        targetX: targetPorts.get(edgeIndex),
        rankVias: rankRoutes[edgeIndex],
        sourceLayer: source.layer,
        targetLayer: target.layer,
        layerCenter: layerY,
        layerHalfHeight: () => NODE_H / 2,
        obstacles,
      });
    });
    edges.forEach((edge, edgeIndex) => {
      const path = appendEdge(group, spec.edgeClass ? spec.edgeClass(edge) : 'dag-edge',
        edgePath(pointSets[edgeIndex]), spec.arrowId);
      incident.get(edge.from).push(path);
      incident.get(edge.to).push(path);
    });
    for (const node of nodes) {
      const position = positions.get(node.id);
      const g = appendBoxNode(group, node, spec.classOf(node), labelOf.get(node.id),
        labelWidth(node.id));
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
      labelOf: (node) => node.title,
      classOf: () => 'dag-node submission',
      // A dependency only the proof package declares is drawn apart: the
      // dependent's statements stand on their own and just its proofs reach
      // across, which is how a proof framework's consumers become visible.
      edgeClass: (edge) => 'dag-edge' + (edge.kind === 'proofs' ? ' proof-dep' : ''),
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

  /** A concept box standing for several statements. It speaks for the claim as
   * a whole; the individual axiom ids belong to the concept page. */
  function conceptTooltipRows(node) {
    const provenCount = node.docks.filter((dock) => dock.proven).length;
    return [
      ['Claim', node.id],
      ...(node.title && node.title !== node.id ? [['Title', node.title]] : []),
      ['Statements', `${node.docks.length} (${provenCount} proven)`],
      ['Status', node.proven ? 'proven' : 'open'],
      ...(node.owner ? [['Submission', node.owner]] : []),
    ];
  }

  /** One dock. Statements of a multi-statement concept are named here by
   * position only — anonymity is the point on this surface, and the raw id is
   * one click away through the dock's link. */
  function dockTooltipRows(node, dock, index) {
    return [
      ['Claim', node.id],
      ['Statement', `${index} of ${node.docks.length}`],
      ['Status', dock.proven ? 'proven' : 'open'],
      ...(dock.owner ? [['Submission', dock.owner]] : []),
    ];
  }

  // Small and tight against the box, so a concept and its docks read as one
  // unit rather than a box with satellites.
  const DOCK_R = 5;
  const DOCK_GAP = 13;
  const DOCK_DROP = 1;

  /** Docks hang in a row under the box's bottom edge, centred on it. */
  function dockOffsetX(node, index) {
    return (index - 1 - (node.docks.length - 1) / 2) * DOCK_GAP;
  }

  function dockCenterY(node) { return node.height / 2 - DOCK_R; }

  function renderProofNetwork(data) {
    const container = document.getElementById('proof-network');
    if (!container || !data || !data.proofs.length) return;
    container.replaceChildren();

    const nodes = [];
    const byKey = new Map();
    // Where each statement is drawn: its own box, or a numbered dock under
    // its home concept's box when that concept declares several statements.
    const placeOf = new Map();
    const conceptNodes = new Map();
    for (const statement of data.statements) {
      // A claim displays as its home concept; a concept declaring several
      // statements is one box with a dock per statement.
      const label = truncate(statement.label || statement.title || statement.id, MAX_LABEL);
      if ((statement.count || 1) > 1 && statement.concept) {
        let node = conceptNodes.get(statement.concept);
        if (!node) {
          node = {
            kind: 'concept', key: 'c:' + statement.concept, id: statement.concept,
            label, title: statement.title, owner: statement.owner, ext: statement.ext,
            href: statement.href ? statement.href.split('#')[0] : undefined,
            docks: [], width: nodeWidth(label), height: NODE_H + DOCK_DROP + 2 * DOCK_R,
          };
          conceptNodes.set(statement.concept, node);
          nodes.push(node);
          byKey.set(node.key, node);
        }
        node.docks[statement.index - 1] = statement;
        placeOf.set(statement.id, { key: node.key, dock: statement.index });
        continue;
      }
      const node = {
        ...statement, kind: 'statement', key: 's:' + statement.id, label,
        width: nodeWidth(label), height: NODE_H,
      };
      nodes.push(node);
      byKey.set(node.key, node);
      placeOf.set(statement.id, { key: node.key });
    }
    for (const node of conceptNodes.values()) {
      // A gap can only come from truncated data; drop it rather than draw a
      // hole, and renumber what is left so every dock keeps a position.
      node.docks = node.docks.filter(Boolean);
      node.docks.forEach((dock, index) => placeOf.set(dock.id, { key: node.key, dock: index + 1 }));
      node.proven = node.docks.every((dock) => dock.proven);
      node.width = Math.max(node.width, node.docks.length * DOCK_GAP + 12);
    }
    for (const proof of data.proofs) {
      const node = { ...proof, kind: 'proof', key: 'p:' + proof.id, width: 28, height: 28 };
      nodes.push(node);
      byKey.set(node.key, node);
    }

    const links = [];
    for (const proof of data.proofs) {
      const proofKey = 'p:' + proof.id;
      // Assumptions name a claim, never which of its statements was used, so
      // several assumed statements of one concept share a single edge.
      const sources = new Map();
      for (const assumption of proof.assumptions) {
        const place = placeOf.get(assumption);
        if (!place) continue;
        const statementIds = sources.get(place.key) || [];
        statementIds.push(assumption);
        sources.set(place.key, statementIds);
      }
      for (const [source, statementIds] of sources) links.push({
        source,
        target: proofKey,
        kind: 'assumption',
        align: sources.size === 1,
        proofId: proof.id,
        statementIds,
      });
      const conclusion = placeOf.get(proof.conclusion);
      if (conclusion) links.push({
        source: proofKey,
        target: conclusion.key,
        kind: 'conclusion',
        align: true,
        dock: conclusion.dock,
        proofId: proof.id,
        statementIds: [proof.conclusion],
      });
    }
    links.sort((a, b) => `${a.source}\0${a.target}`.localeCompare(`${b.source}\0${b.target}`));
    const degrees = new Map(nodes.map((node) => [node.key, { incoming: 0, outgoing: 0 }]));
    for (const link of links) {
      degrees.get(link.source).outgoing += 1;
      degrees.get(link.target).incoming += 1;
    }
    for (const node of nodes) {
      const degree = degrees.get(node.key);
      const ports = Math.max(degree.incoming, degree.outgoing);
      node.width = Math.max(node.width, (ports + 1) * MIN_ARC_SEPARATION);
    }

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
    for (const component of components) component.internalLinkIndices = [];
    links.forEach((link, edgeIndex) => {
      const component = componentOf.get(link.source);
      if (component === componentOf.get(link.target))
        component.internalLinkIndices.push(edgeIndex);
    });

    // Size each SCC. A cyclic component uses one horizontal node row, leaving
    // every node a clear vertical approach from above and below. Its internal
    // links occupy rounded lanes above that row. Singleton components are
    // exactly their node's bounding box.
    for (const component of components) {
      const members = component.members.map((key) => byKey.get(key));
      if (!component.cyclic) {
        component.width = members[0].width;
        component.height = members[0].height;
        members[0].localX = 0;
        members[0].localY = 0;
        continue;
      }
      const contentWidth = members.reduce((sum, node) => sum + node.width, 0) +
        (members.length - 1) * 24;
      const contentHeight = Math.max(...members.map((node) => node.height));
      const laneCount = component.internalLinkIndices.length;
      const topPadding = 38 + Math.max(0, laneCount - 1) * 9;
      const bottomPadding = 16;
      const nodeRowY = (topPadding - bottomPadding) / 2;
      let cursor = -contentWidth / 2;
      members.forEach((node, index) => {
        node.localX = cursor + node.width / 2;
        node.localY = nodeRowY;
        cursor += node.width + (index + 1 < members.length ? 24 : 0);
      });
      component.internalLaneY = new Map(component.internalLinkIndices.map((edgeIndex, slot) => [
        edgeIndex,
        nodeRowY - contentHeight / 2 - 10 - slot * 9,
      ]));
      component.width = contentWidth + 32;
      component.height = contentHeight + topPadding + bottomPadding;
    }

    // Layer and place the condensation DAG with the shared engine; the
    // components are its nodes, keyed by their (unique, deterministic)
    // member list.
    const alignmentPairs = new Set(links
      .filter((link) => link.align &&
        componentOf.get(link.source) !== componentOf.get(link.target))
      .map((link) => `${componentOf.get(link.source).sortKey}\0${componentOf.get(link.target).sortKey}`));
    const componentEdges = [];
    const alignEdgeIndices = [];
    for (const component of components)
      for (const targetId of [...component.outgoing].sort((a, b) => a - b)) {
        const edgeIndex = componentEdges.length;
        componentEdges.push({ from: component.sortKey, to: components[targetId].sortKey });
        if (alignmentPairs.has(`${component.sortKey}\0${components[targetId].sortKey}`))
          alignEdgeIndices.push(edgeIndex);
      }
    const layout = globalThis.laxLayout.layoutDag({
      nodes: components.map((component) => ({ id: component.sortKey, width: component.width })),
      edges: componentEdges,
      nodeGap: 44,
      alignEdgeIndices,
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
    const width = Math.max(
      PROOF_NETWORK_MIN_WIDTH,
      container.clientWidth,
      Math.ceil(layout.width) + 2 * padX,
    );
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
      component.layer = p.layer;
      for (const key of component.members) {
        const node = byKey.get(key);
        node.x = component.x + node.localX;
        node.y = component.y + node.localY;
        node.layer = p.layer;
      }
    }
    const obstacles = nodes;
    const routeOfPair = new Map();
    componentEdges.forEach((edge, index) => {
      routeOfPair.set(`${edge.from}\0${edge.to}`,
        layout.rankRoutes[index].map((p) => ({ x: offsetX + p.x, layer: p.layer })));
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
      return (routeOfPair.get(pairKeyOf(link)) || []).map((p) => ({
        x: p.x + shift,
        layer: p.layer,
      }));
    });
    const crossEnds = (pick) => links.flatMap((link, edgeIndex) => {
      if (componentOf.get(link.source) === componentOf.get(link.target)) return [];
      return [pick(link, edgeIndex)];
    });
    const sourcePorts = portMap(
      crossEnds((link, edgeIndex) => ({ edgeIndex, nodeId: link.source,
        refX: byKey.get(link.target).x })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);
    const targetPorts = portMap(
      crossEnds((link, edgeIndex) => ({ edgeIndex, nodeId: link.target,
        refX: byKey.get(link.source).x })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);
    // A docked conclusion lands on its own dock, not on the box's spread of
    // ports; several proofs concluding one dock fan out inside it.
    const dockedLinks = new Map();
    links.forEach((link, edgeIndex) => {
      if (!link.dock || componentOf.get(link.source) === componentOf.get(link.target)) return;
      const key = `${link.target}\0${link.dock}`;
      if (!dockedLinks.has(key)) dockedLinks.set(key, []);
      dockedLinks.get(key).push(edgeIndex);
    });
    for (const [key, edgeIndices] of dockedLinks) {
      const link = links[edgeIndices[0]];
      const node = byKey.get(link.target);
      const centerX = node.x + dockOffsetX(node, link.dock);
      edgeIndices.forEach((edgeIndex, slot) => {
        targetPorts.set(edgeIndex, centerX + (slot - (edgeIndices.length - 1) / 2) * 3);
      });
    }
    const internalEnds = (pick) => links.flatMap((link, edgeIndex) => {
      if (componentOf.get(link.source) !== componentOf.get(link.target)) return [];
      return [pick(link, edgeIndex)];
    });
    const internalSourcePorts = portMap(
      internalEnds((link, edgeIndex) => ({
        edgeIndex, nodeId: link.source, refX: byKey.get(link.target).x,
      })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);
    const internalTargetPorts = portMap(
      internalEnds((link, edgeIndex) => ({
        edgeIndex, nodeId: link.target, refX: byKey.get(link.source).x,
      })),
      (key) => byKey.get(key).x, (key) => byKey.get(key).width);
    const linkPointSets = links.map((link, edgeIndex) => {
      if (componentOf.get(link.source) === componentOf.get(link.target)) return null;
      const sourceNode = byKey.get(link.source);
      const targetNode = byKey.get(link.target);
      const sourceComponent = componentOf.get(link.source);
      const targetComponent = componentOf.get(link.target);
      return routeDagEdge({
        source: sourceNode,
        target: targetNode,
        sourceX: sourcePorts.get(edgeIndex),
        targetX: targetPorts.get(edgeIndex),
        rankVias: linkVias[edgeIndex],
        sourceLayer: sourceComponent.layer,
        targetLayer: targetComponent.layer,
        layerCenter: (layer) => layerY[layer],
        layerHalfHeight: (layer) => rowHeights[layer] / 2,
        obstacles,
      });
    });
    const incident = new Map(nodes.map((node) => [node.key, []]));
    const dockIncident = new Map();
    const renderedEdges = [];
    links.forEach((link, edgeIndex) => {
      const sourceNode = byKey.get(link.source);
      const targetNode = byKey.get(link.target);
      const sameComponent = componentOf.get(link.source) === componentOf.get(link.target);
      let path;
      if (sameComponent) {
        const excluded = new Set([sourceNode.key, targetNode.key]);
        const directSource = clippedEndpoint(sourceNode, targetNode);
        const directTarget = link.dock
          ? { x: targetNode.x + dockOffsetX(targetNode, link.dock), y: targetNode.y + targetNode.height / 2 }
          : clippedEndpoint(targetNode, sourceNode);
        if (link.source !== link.target &&
          segmentIsClear(directSource, directTarget, obstacles, excluded)) {
          path = edgePath([directSource, directTarget]);
        } else {
          // A blocked internal cycle edge uses its separated lane above the
          // component row; self-loops receive two distinct surface ports.
          const component = componentOf.get(link.source);
          const laneY = component.y + component.internalLaneY.get(edgeIndex);
          let sourceX = internalSourcePorts.get(edgeIndex);
          let targetX = internalTargetPorts.get(edgeIndex);
          if (link.source === link.target) {
            const spread = Math.min(9, sourceNode.width / 4);
            sourceX -= spread;
            targetX += spread;
          }
          path = edgePath([
            { x: sourceX, y: sourceNode.y - sourceNode.height / 2 },
            { x: sourceX, y: laneY },
            { x: targetX, y: laneY },
            { x: targetX, y: targetNode.y - targetNode.height / 2 },
          ]);
        }
      } else {
        // Condensation edges are straight where visible and detour only around
        // actual node obstacles.
        path = edgePath(linkPointSets[edgeIndex]);
      }
      const element = appendEdge(group, `net-edge ${link.kind}`, path, 'proof-arrow');
      renderedEdges.push({ link, path: element, route: element.closest('.graph-edge-route') });
      incident.get(link.source).push(element);
      incident.get(link.target).push(element);
      if (link.dock) {
        const key = `${link.target}\0${link.dock}`;
        if (!dockIncident.has(key)) dockIncident.set(key, []);
        dockIncident.get(key).push(element);
      }
    });

    const nodeItems = [];
    for (const node of nodes) {
      if (node.kind === 'statement') {
        const g = appendBoxNode(group, node, 'net-node ' + (node.proven ? 'proven' : 'open'),
          node.label, node.width, false);
        g.setAttribute('transform', `translate(${node.x},${node.y})`);
        g.setAttribute('aria-label', node.label);
        attachTooltip(g, container, statementTooltipRows(node));
        attachHotEdges(g, incident.get(node.key));
        nodeItems.push({ token: node.key, element: g, node, focusStatement: node.id });
        continue;
      }
      if (node.kind === 'concept') {
        // The box occupies the node's top NODE_H; the docks hang in the strip
        // below it, so an arrow into a dock still arrives at the node's bottom.
        const g = svgEl(group, 'g', { transform: `translate(${node.x},${node.y})` });
        const box = appendBoxNode(g, node, 'net-node ' + (node.proven ? 'proven' : 'open'),
          node.label, node.width, false);
        box.setAttribute('transform', `translate(0,${-node.height / 2 + NODE_H / 2})`);
        box.setAttribute('aria-label', node.label);
        attachTooltip(box, container, conceptTooltipRows(node));
        attachHotEdges(box, incident.get(node.key));
        nodeItems.push({ token: node.key, element: box, node });
        node.docks.forEach((dock, index) => {
          const x = dockOffsetX(node, index + 1);
          const y = dockCenterY(node);
          const dockGroup = svgEl(g, 'g', {
            class: 'net-dock ' + (dock.proven ? 'proven' : 'open') + (dock.ext ? ' ext' : ''),
            'aria-label': `${node.label}, statement ${index + 1} of ${node.docks.length}`,
          });
          svgEl(dockGroup, 'circle', { cx: x, cy: y, r: DOCK_R });
          svgEl(dockGroup, 'text', { x, y, 'text-anchor': 'middle', dy: 2.5 })
            .textContent = String(index + 1);
          attachTooltip(dockGroup, container, dockTooltipRows(node, dock, index + 1));
          attachHotEdges(dockGroup, dockIncident.get(`${node.key}\0${index + 1}`));
          nodeItems.push({ token: `dock:${dock.id}`, element: dockGroup, node,
            focusStatement: dock.id, href: dock.href });
        });
        continue;
      }
      const g = svgEl(group, 'g', {
        class: 'net-proof' + (node.ext ? ' ext' : ''),
        'aria-label': data.details?.[`proof:${node.id}`]?.name || 'Proof',
        transform: `translate(${node.x},${node.y})`,
      });
      svgEl(g, 'rect', {
        x: -node.width / 2, y: -node.height / 2,
        width: node.width, height: node.height, rx: 4,
      });
      svgEl(g, 'text', { 'text-anchor': 'middle', dy: 4.5 }).textContent = '⊢';
      attachTooltip(g, container, proofTooltipRows(node));
      attachHotEdges(g, incident.get(node.key));
      nodeItems.push({ token: node.key, element: g, node });
    }
    installProofSelection(container, data, nodes, byKey, links, nodeItems, renderedEdges);
  }

  function render() {
    if (!globalThis.laxLayout) return;
    const data = readData();
    if (!data) return;
    renderConceptDag(data.concepts);
    renderProofNetwork(data.proofs);
    renderSubmissionDag(data.submissions);
  }

  function installUsedConceptToggle() {
    const button = document.querySelector('[data-used-concepts-toggle]');
    if (!button) return;
    const list = document.getElementById(button.getAttribute('aria-controls'));
    if (!list) return;
    button.addEventListener('click', () => {
      const expanded = list.hidden;
      list.hidden = !expanded;
      button.textContent = `${expanded ? 'Hide' : 'Show'} referenced concepts`;
      button.setAttribute('aria-expanded', String(expanded));
    });
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

  function installProofDetailDismissal() {
    window.addEventListener('click', (event) => {
      const context = activeProofContext;
      if (!context || context.panel.hidden) return;
      const target = event.target;
      if (!(target instanceof Element) || context.panel.contains(target)) return;
      const graphItem = target.closest(
        '.net-node, .net-proof, .net-dock, .graph-edge-route.is-interactive',
      );
      if (graphItem && context.container.contains(graphItem)) return;
      clearProofSelection(context);
    });
    window.addEventListener('keydown', (event) => {
      if (event.key !== 'Escape' || !activeProofContext || activeProofContext.panel.hidden) return;
      event.preventDefault();
      event.stopImmediatePropagation();
      const trigger = activeProofContext.trigger;
      clearProofSelection(activeProofContext);
      trigger?.focus?.();
    });
  }

  function initialize() {
    installUsedConceptToggle();
    installProofDetailDismissal();
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
