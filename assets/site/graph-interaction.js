// Public graph interaction only. Layout, routing, text sizing, and validation
// run before publication. No graph library or custom search engine is loaded.
(() => {
  'use strict';
  let activeGraphTooltip = null;
  let graphTooltipFrame;
  const PROOF_SELECTION_SCALE = 1.28;
  const PROOF_FOCUS_DURATION = 900;
  const reviewCache = new Map();
  let reviewSequence = 0;
  let activeProofController = null;
  let pageProofDetails = {};

  function figureTooltip(container) {
    const figure = container.closest('.graph-figure');
    return figure ? figure.querySelector('.graph-tooltip') : null;
  }

  function positionGraphTooltip(element, tooltip, figure) {
    const gap = 8;
    const inset = 8;
    const figureBox = figure.getBoundingClientRect();
    const expanded = figure.classList.contains('graph-expanded');
    const plotBox = figure.querySelector('.figure-container').getBoundingClientRect();
    const frame = {
      left: expanded ? Math.max(inset, figureBox.left + inset) : inset,
      right: Math.min(window.innerWidth - inset, expanded ? figureBox.right - inset : Infinity),
      top: Math.max(inset, (expanded ? plotBox.top : document.querySelector('.site-header')?.getBoundingClientRect().bottom || 0) + inset),
      bottom: Math.min(window.innerHeight - inset, expanded ? plotBox.bottom - inset : Infinity),
    };
    tooltip.style.maxWidth = Math.min(390, frame.right - frame.left) + 'px';
    const anchor = element.getBoundingClientRect();
    const centerX = (anchor.left + anchor.right) / 2;
    const centerY = (anchor.top + anchor.bottom) / 2;
    const place = (left, top, placement) => {
      // Zoom changes the SVG anchor, not the HTML inspector's scale. Keep
      // its text on the same device-pixel grid as the anchor moves.
      const pixels = window.devicePixelRatio || 1;
      left = Math.round(left * pixels) / pixels;
      top = Math.round(top * pixels) / pixels;
      tooltip.dataset.placement = placement;
      tooltip.style.left = (expanded ? left - figureBox.left - figure.clientLeft : left) + 'px';
      tooltip.style.top = (expanded ? top - figureBox.top - figure.clientTop : top) + 'px';
    };

    if (!expanded) {
      // Use the page margins, including space over the sidebar, so the
      // opaque panel leaves the network unobstructed at the node's height.
      const sides = [
        { name: 'left', space: figureBox.left - gap - frame.left, distance: centerX - figureBox.left },
        { name: 'right', space: frame.right - figureBox.right - gap, distance: figureBox.right - centerX },
      ].sort((a, b) => a.distance - b.distance);
      const style = getComputedStyle(tooltip);
      const padding = parseFloat(style.paddingLeft) + parseFloat(style.paddingRight) + 2;
      const mathWidth = Math.max(0, ...[...tooltip.querySelectorAll('.katex-html')]
        .map((math) => math.getBoundingClientRect().width));
      const minWidth = Math.min(tooltip.offsetWidth, Math.max(140, mathWidth + padding));
      for (const side of sides) {
        if (side.space < minWidth) continue;
        tooltip.style.maxWidth = Math.min(390, side.space) + 'px';
        const width = tooltip.offsetWidth;
        const height = tooltip.offsetHeight;
        if (height > frame.bottom - frame.top) continue;
        const left = side.name === 'left' ? figureBox.left - gap - width : figureBox.right + gap;
        const top = Math.max(frame.top, Math.min(centerY - height / 2, frame.bottom - height));
        place(left, top, side.name);
        return;
      }

      // A narrow screen may have no usable side margin. Prefer an opaque
      // panel below the figure, or above it if only that space is visible.
      tooltip.style.maxWidth = Math.min(390, frame.right - frame.left) + 'px';
      const width = tooltip.offsetWidth;
      const height = tooltip.offsetHeight;
      const left = Math.max(frame.left, Math.min(
        sides[0].name === 'left' ? figureBox.left : figureBox.right - width,
        frame.right - width,
      ));
      if (figureBox.bottom + gap + height <= frame.bottom) {
        place(left, figureBox.bottom + gap, 'below');
        return;
      }
      if (figureBox.top - gap - height >= frame.top) {
        place(left, figureBox.top - gap - height, 'above');
        return;
      }
      // If the network fills the viewport, keep the panel readable nearby.
    }

    const width = tooltip.offsetWidth;
    const height = tooltip.offsetHeight;
    const overlap = (a, b) => Math.max(0, Math.min(a.right, b.right) - Math.max(a.left, b.left)) *
      Math.max(0, Math.min(a.bottom, b.bottom) - Math.max(a.top, b.top));
    const padded = (box, padding) => ({
      left: box.left - padding, right: box.right + padding,
      top: box.top - padding, bottom: box.bottom + padding,
    });
    const candidates = [
      [centerX - width / 2, anchor.top - height - gap],
      [centerX - width / 2, anchor.bottom + gap],
      [anchor.right + gap, centerY - height / 2],
      [anchor.left - width - gap, centerY - height / 2],
    ].map(([left, top]) => {
      left = Math.max(frame.left, Math.min(left, frame.right - width));
      top = Math.max(frame.top, Math.min(top, frame.bottom - height));
      return { left, top, right: left + width, bottom: top + height };
    });

    // In the large window, stay beside the hovered node and leave it visible.
    const protectedAnchor = padded(anchor, gap);
    const ranked = candidates.map((box) => ({
      box,
      score: [
        overlap(box, protectedAnchor),
        (box.left + width / 2 - centerX) ** 2 + (box.top + height / 2 - centerY) ** 2,
      ],
    })).sort((a, b) => {
      for (let i = 0; i < a.score.length; i++)
        if (a.score[i] !== b.score[i]) return a.score[i] - b.score[i];
      return 0;
    });
    const best = ranked[0].box;
    place(best.left, best.top, 'near');
  }

  function showTooltip(container, element, content, renderedHtml) {
    const tooltip = figureTooltip(container);
    const figure = tooltip && tooltip.closest('.graph-figure');
    if (!tooltip || !figure) return;
    tooltip.replaceChildren();
    if (typeof renderedHtml === 'string') {
      // Only build-time Markdown/KaTeX output goes here; author HTML is
      // escaped by the renderer before it enters the inert graph payload.
      tooltip.innerHTML = renderedHtml;
    } else if (typeof content === 'string') {
      tooltip.textContent = content;
    } else {
      for (const [label, value] of content) {
        const row = document.createElement('div');
        const heading = document.createElement('strong');
        heading.textContent = label + ': ';
        row.append(heading, document.createTextNode(value));
        tooltip.append(row);
      }
    }
    tooltip.hidden = !tooltip.textContent.trim();
    if (tooltip.hidden) {
      hideTooltip(container);
      return;
    }
    positionGraphTooltip(element, tooltip, figure);
    activeGraphTooltip = { container, element, tooltip, figure };
    document.fonts?.ready.then(refreshGraphTooltip);
  }

  function hideTooltip(container) {
    const tooltip = figureTooltip(container);
    if (tooltip) tooltip.hidden = true;
    if (activeGraphTooltip?.container === container) activeGraphTooltip = null;
  }

  function refreshGraphTooltip() {
    if (!activeGraphTooltip) return;
    cancelAnimationFrame(graphTooltipFrame);
    graphTooltipFrame = requestAnimationFrame(() => {
      if (!activeGraphTooltip) return;
      const { container, element, tooltip, figure } = activeGraphTooltip;
      const node = element.getBoundingClientRect();
      const plot = container.getBoundingClientRect();
      if (node.right <= Math.max(0, plot.left) || node.left >= Math.min(window.innerWidth, plot.right) ||
          node.bottom <= Math.max(0, plot.top) || node.top >= Math.min(window.innerHeight, plot.bottom)) {
        hideTooltip(container);
        return;
      }
      positionGraphTooltip(element, tooltip, figure);
    });
  }

  function attachTooltip(el, container, content, renderedHtml) {
    el.addEventListener('mouseenter', () => showTooltip(container, el, content, renderedHtml));
    el.addEventListener('mouseleave', () => {
      if (!el.contains(document.activeElement)) hideTooltip(container);
    });
    el.addEventListener('focus', () => showTooltip(container, el, content, renderedHtml));
    el.addEventListener('blur', () => {
      if (!el.matches(':hover')) hideTooltip(container);
    });
  }

  // ---- focused proof-network details ----

  function appendText(parent, name, className, value) {
    const element = document.createElement(name);
    if (className) element.className = className;
    element.textContent = value;
    parent.append(element);
    return element;
  }

  /** All HTML here was rendered and sanitized by the build-time Markdown
   * renderer before it entered the inert graph payload. */
  function appendRendered(parent, className, html) {
    if (!html) return null;
    const element = document.createElement('div');
    element.className = className;
    element.innerHTML = html;
    parent.append(element);
    return element;
  }

  function ensureDetailPanel(controller) {
    const figure = controller.container.closest('.graph-figure');
    let panel = figure.querySelector('.graph-detail-panel');
    if (panel) return panel;
    panel = document.createElement('aside');
    panel.className = 'graph-detail-panel graph-detail-right';
    panel.hidden = true;
    panel.setAttribute('aria-label', 'Graph details');
    const close = appendText(panel, 'button', 'graph-detail-close', '×');
    close.type = 'button';
    close.setAttribute('aria-label', 'Close graph details');
    close.addEventListener('click', () => {
      const trigger = controller.selectionTrigger;
      clearProofSelection(controller);
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
    if (!host?.startsWith('https://')) {
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
        }).catch((error) => {
          reviewCache.delete(detail.reviewUrl);
          throw error;
        });
      reviewCache.set(detail.reviewUrl, request);
    }
    request.then((data) => {
      if (panel.dataset.reviewToken !== token) return;
      values.replaceChildren();
      const endorsements = Number(data.counts?.endorse) || 0;
      const flags = Number(data.counts?.flag) || 0;
      appendText(values, 'span', 'graph-detail-review-count endorse',
        `🥳 ${endorsements} endorsement${endorsements === 1 ? '' : 's'}`);
      appendText(values, 'span', 'graph-detail-review-count flag',
        `🚩 ${flags} flag${flags === 1 ? '' : 's'}`);
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
    if (claim.statement)
      row.append(document.createTextNode(` (statement ${claim.statement} of ${claim.statementCount})`));
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
    if (!detail.statements?.length) return;
    const section = document.createElement('section');
    appendText(section, 'h4', '', 'Lean formalization');
    for (const statement of detail.statements) {
      const block = document.createElement('div');
      block.className = 'graph-detail-formalization' +
        (focusStatement === statement.id ? ' is-focused' : '');
      if (detail.statements.length > 1)
        appendText(block, 'p', 'graph-detail-formalization-label',
          `${statement.name} · ${statement.proven ? 'proven' : 'open'}`);
      const href = statement.href || detail.href;
      const preview = document.createElement(href ? 'a' : 'div');
      preview.className = 'graph-detail-formalization-preview inline-contract-shell';
      if (href) {
        preview.href = href;
        preview.setAttribute('aria-label', `Open the full Lean source for ${detail.name}`);
      }
      const pre = document.createElement('pre');
      appendText(pre, 'code', '', statement.signature);
      preview.append(pre);
      if (href) appendText(preview, 'span', 'graph-detail-formalization-open', 'Open full Lean source →');
      block.append(preview);
      section.append(block);
    }
    parent.append(section);
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
      code.title = detail.leanPath;
      if (detail.sourceHref) {
        const link = document.createElement('a');
        link.className = 'graph-detail-source-link';
        link.href = detail.sourceHref;
        link.textContent = 'View source';
        source.append(link);
      }
      parent.append(source);
    }
  }

  function renderDetailPanel(controller, view) {
    const panel = ensureDetailPanel(controller);
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
      if (view.proofDetail.href) {
        const link = document.createElement('a');
        link.href = view.proofDetail.href;
        link.textContent = view.proofDetail.name;
        proof.append(link);
      } else appendText(proof, 'p', '', view.proofDetail.name);
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
    const controls = panel.parentElement.querySelector('.graph-controls');
    panel.style.top = `${(controls?.offsetHeight || 0) + 6}px`;
    scroll.scrollTop = 0;
    return panel;
  }

  function detailForInfo(controller, info) {
    if (!info) return null;
    if (info.kind === 'proof') return controller.details[`proof:${info.semanticId}`] || null;
    if (info.kind === 'concept') return controller.details[`concept:${info.semanticId}`] || null;
    return Object.values(controller.details).find((detail) => detail.kind === 'concept' &&
      detail.statements?.some((statement) => statement.id === info.semanticId)) || null;
  }

  function graphClosure(interaction, roots) {
    const nodeIds = new Set(Object.values(interaction.nodes).map((node) => node.nodeId));
    const successors = new Map([...nodeIds].map((id) => [id, []]));
    const predecessors = new Map([...nodeIds].map((id) => [id, []]));
    for (const edge of Object.values(interaction.edges || {})) {
      successors.get(edge.source)?.push(edge.target);
      predecessors.get(edge.target)?.push(edge.source);
    }
    const related = new Set(roots);
    const visit = (adjacency, root) => {
      const seen = new Set([root]), pending = [root];
      while (pending.length) {
        const id = pending.pop();
        for (const next of adjacency.get(id) || []) {
          if (seen.has(next)) continue;
          seen.add(next); related.add(next); pending.push(next);
        }
      }
    };
    for (const root of roots) {
      visit(successors, root);
      visit(predecessors, root);
    }
    return related;
  }

  function stopCameraAnimation(controller) {
    if (controller.cameraAnimation) cancelAnimationFrame(controller.cameraAnimation);
    controller.cameraAnimation = null;
  }

  function animateCamera(controller, target) {
    stopCameraAnimation(controller);
    if (matchMedia('(prefers-reduced-motion: reduce)').matches) {
      controller.camera = target;
      controller.paint();
      return;
    }
    const start = { ...controller.camera }, began = performance.now();
    const step = (now) => {
      const progress = Math.min(1, (now - began) / PROOF_FOCUS_DURATION);
      const eased = progress < 0.5 ? 4 * progress ** 3 : 1 - (-2 * progress + 2) ** 3 / 2;
      controller.camera = {
        x: start.x + (target.x - start.x) * eased,
        y: start.y + (target.y - start.y) * eased,
        scale: start.scale + (target.scale - start.scale) * eased,
      };
      controller.paint();
      if (progress < 1) controller.cameraAnimation = requestAnimationFrame(step);
      else controller.cameraAnimation = null;
    };
    controller.cameraAnimation = requestAnimationFrame(step);
  }

  function focusProofSelection(controller) {
    const edge = controller.selection.type === 'edge'
      ? controller.interaction.edges[controller.selection.id] : null;
    const node = controller.selection.type === 'node'
      ? controller.interaction.nodes[controller.selection.id] : null;
    const focusIds = new Set(edge ? [edge.source, edge.target] : [node?.nodeId]);
    const elements = [...controller.container.querySelectorAll('[data-node-id]')]
      .filter((element) => focusIds.has(controller.interaction.nodes[element.dataset.nodeId]?.nodeId));
    if (!elements.length) return;
    const boxes = elements.map((element) => element.getBoundingClientRect());
    const focus = {
      x: (Math.min(...boxes.map((box) => box.left)) + Math.max(...boxes.map((box) => box.right))) / 2,
      y: (Math.min(...boxes.map((box) => box.top)) + Math.max(...boxes.map((box) => box.bottom))) / 2,
    };
    const plot = controller.container.getBoundingClientRect();
    const panelWidth = controller.panel.offsetWidth < controller.container.clientWidth * 0.8
      ? controller.panel.offsetWidth : 0;
    const desired = { x: plot.left + (plot.width - panelWidth) / 2, y: plot.top + plot.height / 2 };
    const matrix = controller.svg.getScreenCTM();
    if (!matrix) return;
    const inverse = matrix.inverse();
    const at = new DOMPoint(focus.x, focus.y).matrixTransform(inverse);
    const destination = new DOMPoint(desired.x, desired.y).matrixTransform(inverse);
    const targetScale = Math.min(4, controller.selectionBaseScale * PROOF_SELECTION_SCALE);
    const ratio = targetScale / controller.camera.scale;
    animateCamera(controller, {
      x: at.x - (at.x - controller.camera.x) * ratio + destination.x - at.x,
      y: at.y - (at.y - controller.camera.y) * ratio + destination.y - at.y,
      scale: targetScale,
    });
  }

  function setProofSelectionClasses(controller, descriptor) {
    for (const element of controller.container.querySelectorAll('[data-node-id]')) {
      const info = controller.interaction.nodes[element.dataset.nodeId];
      const selected = descriptor.type === 'node' && descriptor.id === element.dataset.nodeId;
      const related = controller.related.has(info?.nodeId);
      element.classList.toggle('graph-selected', selected);
      element.classList.toggle('graph-related', related && !selected);
      element.classList.toggle('graph-dimmed', !related);
    }
    for (const path of controller.container.querySelectorAll('[data-edge-id]')) {
      const edge = controller.interaction.edges?.[path.dataset.edgeId];
      const selected = descriptor.type === 'edge' && descriptor.id === path.dataset.edgeId;
      const related = edge && controller.related.has(edge.source) && controller.related.has(edge.target);
      path.classList.toggle('graph-selected', selected);
      path.classList.toggle('graph-related', related && !selected);
      path.classList.toggle('graph-dimmed', !related);
    }
  }

  function clearProofSelection(controller, restoreScale = true) {
    if (!controller?.selection) return;
    stopCameraAnimation(controller);
    for (const element of controller.container.querySelectorAll(
      '[data-node-id], [data-edge-id]',
    )) element.classList.remove('graph-selected', 'graph-related', 'graph-dimmed');
    const baseScale = controller.selectionBaseScale;
    controller.selection = null;
    controller.related = null;
    controller.selectionTrigger = null;
    if (controller.panel) {
      controller.panel.hidden = true;
      delete controller.panel.dataset.reviewToken;
    }
    if (restoreScale && baseScale && controller.camera.scale !== baseScale) {
      const plot = controller.container.getBoundingClientRect();
      const matrix = controller.svg.getScreenCTM();
      if (matrix) {
        const center = new DOMPoint(plot.left + plot.width / 2, plot.top + plot.height / 2)
          .matrixTransform(matrix.inverse());
        const contentX = (center.x - controller.camera.x) / controller.camera.scale;
        const contentY = (center.y - controller.camera.y) / controller.camera.scale;
        controller.camera = { x: center.x - contentX * baseScale,
          y: center.y - contentY * baseScale, scale: baseScale };
        controller.paint();
      }
    }
    controller.selectionBaseScale = null;
    if (activeProofController === controller) activeProofController = null;
  }

  function selectProofItem(controller, descriptor, trigger, view) {
    if (activeProofController && activeProofController !== controller)
      clearProofSelection(activeProofController);
    if (!controller.selection) controller.selectionBaseScale = controller.camera.scale;
    activeProofController = controller;
    controller.autoFrame = false;
    controller.selection = descriptor;
    controller.selectionTrigger = trigger;
    const edge = descriptor.type === 'edge' ? controller.interaction.edges[descriptor.id] : null;
    const info = descriptor.type === 'node' ? controller.interaction.nodes[descriptor.id] : null;
    controller.related = graphClosure(controller.interaction,
      edge ? [edge.source, edge.target] : [info.nodeId]);
    setProofSelectionClasses(controller, descriptor);
    controller.panel = renderDetailPanel(controller, view);
    hideTooltip(controller.container);
    requestAnimationFrame(() => focusProofSelection(controller));
  }

  function activateProofItem(controller, event, select) {
    const figure = controller.container.closest('.graph-figure');
    event.preventDefault();
    event.stopPropagation();
    if (figure.classList.contains('graph-expanded')) {
      select();
      return;
    }
    const button = figure.querySelector('[data-graph-expand]');
    if (!button) return;
    setExpanded(button, true);
    // setExpanded frames the drawing on its next animation frame. Select
    // afterwards so the focus zoom starts from that large-window framing.
    requestAnimationFrame(() => {
      if (figure.classList.contains('graph-expanded')) select();
    });
  }

  function installProofSelection(container, controller, interaction) {
    if (container.id !== 'proof-network' || !Object.keys(controller.details).length) return;
    controller.interaction = interaction;
    for (const element of container.querySelectorAll('[data-node-id]')) {
      const info = interaction.nodes[element.dataset.nodeId];
      const detail = detailForInfo(controller, info);
      if (!detail) continue;
      const activate = (event) => {
        const trigger = event.currentTarget;
        const eyebrow = info.kind === 'proof' ? 'Proof'
          : detail.type ? detail.type.charAt(0).toUpperCase() + detail.type.slice(1) : 'Claim';
        activateProofItem(controller, event, () => {
          selectProofItem(controller, { type: 'node', id: element.dataset.nodeId }, trigger, {
            detail, eyebrow,
            focusStatement: ['statement', 'dock'].includes(info.kind) ? info.semanticId : undefined,
            href: info.href || detail.href,
            actionLabel: info.kind === 'proof' ? 'Open proof page' : 'Open concept page',
          });
        });
      };
      element.addEventListener('click', activate);
      if (!element.matches('a')) element.addEventListener('keydown', (event) => {
        if (event.key === 'Enter' || event.key === ' ') activate(event);
      });
    }
    const hits = new Map();
    for (const hit of container.querySelectorAll('[data-edge-hit]')) {
      const paths = hits.get(hit.dataset.edgeHit) || [];
      paths.push(hit); hits.set(hit.dataset.edgeHit, paths);
    }
    for (const [edgeId, elements] of hits) {
      const edge = interaction.edges[edgeId];
      if (!edge) continue;
      const sourceInfo = interaction.nodes[edge.source], targetInfo = interaction.nodes[edge.target];
      const proofInfo = sourceInfo.kind === 'proof' ? sourceInfo : targetInfo;
      const claimInfo = sourceInfo.kind === 'proof' ? targetInfo : sourceInfo;
      const proofDetail = detailForInfo(controller, proofInfo);
      const claimDetail = detailForInfo(controller, claimInfo);
      if (!proofDetail || !claimDetail) continue;
      const assumption = edge.kind === 'assumption';
      const label = assumption
        ? `${claimDetail.name}, assumption of ${proofDetail.name}`
        : `${proofDetail.name}, conclusion ${claimDetail.name}`;
      const activate = (event) => {
        const trigger = event.currentTarget;
        activateProofItem(controller, event, () => {
          selectProofItem(controller, { type: 'edge', id: edgeId }, trigger, {
            detail: claimDetail,
            eyebrow: assumption ? 'Assumption link' : 'Conclusion link',
            name: claimDetail.name,
            relation: assumption
              ? `${claimDetail.name} is used as an assumption of ${proofDetail.name}.`
              : `${proofDetail.name} establishes ${claimDetail.name}.`,
            proofDetail,
            focusStatement: assumption ? edge.sourceSemanticId : edge.targetSemanticId,
            href: proofDetail.href,
            actionLabel: 'Open proof page',
          });
        });
      };
      elements.forEach((hit, index) => {
        hit.setAttribute('aria-label', label);
        hit.addEventListener('click', activate);
        const hot = () => {
          for (const path of controller.edgePaths.get(edgeId) || []) path.classList.add('hot');
        };
        const cold = () => {
          for (const path of controller.edgePaths.get(edgeId) || []) path.classList.remove('hot');
        };
        hit.addEventListener('mouseenter', hot);
        hit.addEventListener('mouseleave', cold);
        hit.addEventListener('focus', hot);
        hit.addEventListener('blur', cold);
        if (index === 0) hit.addEventListener('keydown', (event) => {
          if (event.key === 'Enter' || event.key === ' ') activate(event);
        });
      });
    }
    enableProofInteraction(controller);
  }

  function enableProofInteraction(controller) {
    if (controller.container.id !== 'proof-network') return;
    const seen = new Set();
    for (const hit of controller.container.querySelectorAll('[data-edge-hit]')) {
      if (!seen.has(hit.dataset.edgeHit)) {
        hit.setAttribute('tabindex', '0');
        hit.setAttribute('role', 'button');
        seen.add(hit.dataset.edgeHit);
      } else {
        hit.removeAttribute('tabindex');
        hit.removeAttribute('role');
      }
    }
  }

  const controllers = new Map();
  let expandedFigure = null;
  const previousAttributes = new WeakMap();

  function bindView(container, controller, interaction) {
    const svg = container.querySelector('svg');
    if (!svg) return;
    const cameraGroup = svg.querySelector('[data-graph-camera]');
    const edges = new Map();
    for (const path of svg.querySelectorAll('[data-edge-id]')) {
      const paths = edges.get(path.dataset.edgeId) || [];
      paths.push(path); edges.set(path.dataset.edgeId, paths);
    }
    controller.container = container;
    controller.svg = svg;
    controller.cameraElement = cameraGroup;
    controller.edgePaths = edges;
    controller.camera = { x: 0, y: 0, scale: 1 };
    controller.fitScrollbars = () => {
      if (!container.clientWidth || !container.clientHeight) return;
      const matrix = svg.getScreenCTM();
      if (!matrix) return;
      const width = svg.viewBox.baseVal.width * matrix.a * controller.camera.scale;
      const height = svg.viewBox.baseVal.height * matrix.d * controller.camera.scale;
      // The SVG keeps its original dimensions for stable coordinates. After
      // zooming out those dimensions must not force unused scrollbars. Solve
      // each axis, including space consumed by a scrollbar on the other axis.
      container.style.overflowX = 'hidden';
      container.style.overflowY = 'hidden';
      for (let pass = 0; pass < 2; pass++) {
        container.style.overflowX = width > container.clientWidth + 1 ? 'auto' : 'hidden';
        container.style.overflowY = height > container.clientHeight + 1 ? 'auto' : 'hidden';
      }
    };
    let frame;
    let paintedScale;
    const constrainVertical = () => {
      if (!container.clientHeight || getComputedStyle(container).overflowY !== 'hidden') return;
      // Hidden overflow can retain a native scroll offset after zoom/focus.
      // When the drawing fits, its full published bounds (including margins)
      // must remain between the controls and legend, even while dragging.
      container.scrollTop = 0;
      const matrix = svg.getScreenCTM();
      if (!matrix || matrix.d <= 0) return;
      const bounds = svg.viewBox.baseVal, camera = controller.camera;
      const height = bounds.height * camera.scale;
      const available = container.clientHeight / matrix.d;
      if (height > available + 1 / matrix.d) return;
      const top = (container.getBoundingClientRect().top + container.clientTop - matrix.f) / matrix.d;
      const minimum = top - bounds.y * camera.scale;
      const maximum = minimum + Math.max(0, available - height);
      camera.y = Math.max(minimum, Math.min(maximum, camera.y));
    };
    const paint = () => {
      frame = null;
      if (controller.camera.scale !== paintedScale) { controller.fitScrollbars(); paintedScale = controller.camera.scale; }
      constrainVertical();
      const { x, y, scale } = controller.camera;
      cameraGroup.setAttribute('transform', `translate(${x},${y}) scale(${scale})`);
      const output = container.closest('.graph-figure').querySelector('[data-graph-zoom-status]');
      if (output) output.value = `${Math.round(scale * 100)}%`;
      refreshGraphTooltip();
    };
    controller.paint = () => { if (!frame) frame = requestAnimationFrame(paint); };
    controller.restoreInline = (view) => {
      stopCameraAnimation(controller);
      controller.autoFrame = false;
      controller.camera = { ...view.camera };
      paint();
      container.scrollLeft = view.left;
      container.scrollTop = view.top;
    };
    controller.frameExpanded = () => {
      stopCameraAnimation(controller);
      if (!container.clientWidth || !container.clientHeight) return;
      const bounds = svg.viewBox.baseVal;
      if (!bounds.width || !bounds.height) return;
      const inset = 16;
      // Published labels are 12px. Automatic framing keeps them at 12–18px:
      // fill the available space where possible, without inflating tiny graphs
      // or shrinking a large graph into an unreadable overview.
      container.style.overflowX = 'hidden';
      container.style.overflowY = 'hidden';
      const fit = Math.min((container.clientWidth - 2 * inset) / bounds.width,
        (container.clientHeight - 2 * inset) / bounds.height);
      const scale = Math.max(1, Math.min(1.5, fit)) / svg.getScreenCTM().a;
      controller.camera = { x: 0, y: 0, scale };
      cameraGroup.setAttribute('transform', `scale(${scale})`);
      controller.fitScrollbars();
      container.scrollTop = 0;
      container.scrollLeft = Math.max(0, (container.scrollWidth - container.clientWidth) / 2);
      const matrix = svg.getScreenCTM(), box = container.getBoundingClientRect();
      const width = bounds.width * scale * matrix.a, height = bounds.height * scale * matrix.d;
      const target = new DOMPoint(box.left + container.clientLeft + (container.clientWidth - width) / 2,
        box.top + container.clientTop + (height <= container.clientHeight ? (container.clientHeight - height) / 2 : inset))
        .matrixTransform(matrix.inverse());
      controller.camera.x = target.x - bounds.x * scale;
      controller.camera.y = target.y - bounds.y * scale;
      controller.autoFrame = true;
      paint();
    };
    controller.zoom = (factor, clientPoint) => {
      stopCameraAnimation(controller);
      controller.autoFrame = false;
      const camera = controller.camera;
      const scale = Math.max(0.2, Math.min(4, camera.scale * factor));
      const ratio = scale / camera.scale;
      const matrix = svg.getScreenCTM().inverse();
      const box = container.getBoundingClientRect();
      const at = new DOMPoint(clientPoint?.x ?? (box.left + box.width / 2), clientPoint?.y ?? (box.top + box.height / 2)).matrixTransform(matrix);
      camera.x = at.x - (at.x - camera.x) * ratio;
      camera.y = at.y - (at.y - camera.y) * ratio;
      camera.scale = scale;
      if (controller.selection) controller.selectionBaseScale = scale / PROOF_SELECTION_SCALE;
      controller.paint();
    };
    controller.reset = () => {
      stopCameraAnimation(controller);
      if (container.closest('.graph-figure').classList.contains('graph-expanded')) {
        controller.frameExpanded();
        if (controller.selection) controller.selectionBaseScale = controller.camera.scale;
        return;
      }
      controller.autoFrame = false;
      controller.camera = { x: 0, y: 0, scale: 1 }; controller.paint();
      container.scrollTop = 0;
      container.scrollLeft = Math.max(0, (container.scrollWidth - container.clientWidth) / 2);
    };
    for (const element of svg.querySelectorAll('[data-node-id]')) {
      const info = interaction.nodes[element.dataset.nodeId];
      if (!info) continue;
      const incident = info.incident.flatMap((id) => edges.get(id) || []);
      const hot = () => { controller.anchorId = element.dataset.nodeId; for (const edge of incident) edge.classList.add('hot'); };
      const cold = () => { for (const edge of incident) edge.classList.remove('hot'); };
      element.addEventListener('mouseenter', hot);
      element.addEventListener('mouseleave', cold);
      element.addEventListener('focus', hot);
      element.addEventListener('blur', cold);
      attachTooltip(element, container, info.tooltipRows ?? info.label, info.tooltipHtml);
    }
    installProofSelection(container, controller, interaction);
    let drag = null;
    svg.addEventListener('pointerdown', (event) => {
      // Native one-finger page/viewport scrolling remains available on touch.
      if (event.pointerType === 'touch' || event.button !== 0 ||
          event.target.closest('a, [data-edge-hit]')) return;
      stopCameraAnimation(controller);
      controller.autoFrame = false;
      const matrix = svg.getScreenCTM();
      drag = { id: event.pointerId, x: event.clientX, y: event.clientY, scale: matrix.a };
      svg.setPointerCapture(event.pointerId); svg.classList.add('graph-dragging');
      hideTooltip(container);
    });
    svg.addEventListener('pointermove', (event) => {
      if (!drag || event.pointerId !== drag.id) return;
      controller.camera.x += (event.clientX - drag.x) / drag.scale;
      controller.camera.y += (event.clientY - drag.y) / drag.scale;
      drag.x = event.clientX; drag.y = event.clientY; controller.paint();
    });
    const release = () => { drag = null; svg.classList.remove('graph-dragging'); };
    svg.addEventListener('pointerup', release); svg.addEventListener('pointercancel', release);
    svg.addEventListener('wheel', (event) => {
      if (!event.ctrlKey && !event.metaKey) return;
      event.preventDefault();
      controller.zoom(Math.exp(-Math.max(-120, Math.min(120, event.deltaY)) / 250), { x: event.clientX, y: event.clientY });
    }, { passive: false });
    controller.reset();
  }

  async function switchView(container, controller, state) {
    const view = controller.data.views[state];
    if (!view) return;
    const request = ++controller.request;
    const previous = controller.anchorId && [...container.querySelectorAll('[data-node-id]')].find((node) => node.dataset.nodeId === controller.anchorId);
    const anchor = previous?.getBoundingClientRect();
    try {
      let ready = view;
      if (!ready.svg && ready.src) {
        const url = new URL(ready.src, location.href);
        if (url.origin !== location.origin) throw new Error('Graph geometry must be served from this site.');
        const response = await fetch(url);
        if (!response.ok) throw new Error('This graph view could not be loaded.');
        const loaded = await response.json();
        ready = { ...view, ...loaded }; controller.data.views[state] = ready;
      }
      if (request !== controller.request) return;
      if (!ready.svg) throw new Error('This export does not contain the selected view. Use a self-contained graph export.');
      hideTooltip(container);
      clearProofSelection(controller, false);
      // A complete validated SVG replaces all nodes AND routes together.
      container.innerHTML = ready.svg;
      container.style.height = `${Math.min(ready.height || 720, 720)}px`;
      controller.state = state;
      bindView(container, controller, ready.interaction);
      updateControls(container, controller);
      if (anchor && controller.anchorId && !controller.autoFrame) {
        const selected = [...container.querySelectorAll('[data-node-id]')].find((node) => node.dataset.nodeId === controller.anchorId);
        if (selected) {
          const now = selected.getBoundingClientRect(), scale = controller.svg.getScreenCTM().a;
          controller.camera.x += (anchor.left - now.left) / scale;
          controller.camera.y += (anchor.top - now.top) / scale; controller.paint();
        }
      }
    } catch (error) {
      const status = container.closest('.graph-figure').querySelector('[data-graph-view-status], #concept-graph-status');
      if (status) status.textContent = error.message;
    }
  }

  function updateControls(container, controller) {
    const figure = container.closest('.graph-figure'), data = controller.data;
    for (const [id, index, name, count] of [['concept-expand', 0, 'ancestors', data.ancestors], ['concept-descend', 1, 'descendants', data.descendants]]) {
      const button = figure.querySelector(`#${id}`);
      if (!button) continue;
      const on = controller.state[index] === '1';
      button.disabled = !count;
      button.textContent = count ? `${on ? 'Hide' : 'Show'} ${name}` : `No ${name}`;
      button.setAttribute('aria-pressed', String(on && count > 0));
      button.onclick = () => {
        const state = controller.state.split(''); state[index] = on ? '0' : '1';
        switchView(container, controller, state.join(''));
      };
    }
    const status = figure.querySelector('#concept-graph-status');
    if (status) status.textContent = data.views[controller.state].status;
  }

  function setExpanded(button, expanded) {
    const figure = button.closest('.graph-figure');
    const container = figure.querySelector('.figure-container'), controller = controllers.get(container.id);
    if (expanded && expandedFigure && expandedFigure !== figure) setExpanded(expandedFigure.querySelector('[data-graph-expand]'), false);
    if (!expanded && controller) clearProofSelection(controller, false);
    if (expanded) {
      if (controller) controller.inlineView = { state: controller.state, camera: { ...controller.camera },
        left: container.scrollLeft, top: container.scrollTop };
      previousAttributes.set(figure, ['role', 'aria-modal', 'aria-label'].map((name) => [name, figure.getAttribute(name)]));
      figure.setAttribute('role', 'dialog'); figure.setAttribute('aria-modal', 'true');
      figure.setAttribute('aria-label', `${button.dataset.graphLabel || 'Graph'} large view`);
    } else for (const [name, value] of previousAttributes.get(figure) || []) {
      if (value === null) figure.removeAttribute(name); else figure.setAttribute(name, value);
    }
    figure.classList.toggle('graph-expanded', expanded);
    button.setAttribute('aria-expanded', String(expanded));
    button.setAttribute('aria-label', `${expanded ? 'Close' : 'Open'} ${button.dataset.graphLabel || 'graph'} large window`);
    expandedFigure = expanded ? figure : null;
    document.body.classList.toggle('graph-window-open', Boolean(expandedFigure));
    hideTooltip(container);
    // Frame the same complete geometry in the new viewport. Closing restores
    // the inline camera instead of carrying the large-window zoom into the page.
    requestAnimationFrame(() => {
      if (!controller || figure.classList.contains('graph-expanded') !== expanded) return;
      if (expanded) controller.frameExpanded();
      else if (controller.inlineView?.state === controller.state) {
        controller.restoreInline(controller.inlineView);
      } else controller.reset();
    });
  }

  function installContainer(container, data, details = {}) {
    const figure = container.closest('.graph-figure');
    data.views[data.initial].svg ||= container.querySelector('svg')?.outerHTML;
    const controller = { data, details, state: data.initial, request: 0 };
    controllers.set(container.id, controller);
    bindView(container, controller, data.views[data.initial].interaction);
    new ResizeObserver(() => {
      if (controller.autoFrame && figure.classList.contains('graph-expanded')) controller.frameExpanded();
      else { controller.fitScrollbars(); controller.paint(); }
    }).observe(container);
    container.addEventListener('scroll', () => {
      if (container.scrollTop && getComputedStyle(container).overflowY === 'hidden') controller.paint();
    }, { passive: true });
    updateControls(container, controller);
    for (const button of figure.querySelectorAll('[data-graph-zoom]')) {
      button.disabled = false;
      button.addEventListener('click', () => button.dataset.graphZoom === 'reset' ? controller.reset() : controller.zoom(button.dataset.graphZoom === 'in' ? 1.2 : 1 / 1.2));
    }
    container.addEventListener('keydown', (event) => {
      if (event.key === '+' || event.key === '=') { event.preventDefault(); controller.zoom(1.2); }
      if (event.key === '-') { event.preventDefault(); controller.zoom(1 / 1.2); }
      if (event.key === '0') { event.preventDefault(); controller.reset(); }
    });
    container.closest('details')?.addEventListener('toggle', () => {
      if (!container.closest('details').open) return;
      container.scrollTop = 0; container.scrollLeft = Math.max(0, (container.scrollWidth - container.clientWidth) / 2);
    });
  }

  function initialize() {
    const raw = document.getElementById('graph-data');
    let payload, data;
    try {
      payload = JSON.parse(raw?.textContent || '{}');
      data = payload.prepared;
      pageProofDetails = payload.proofs?.details || {};
    } catch { return; }
    if (data) for (const [id, descriptor] of Object.entries(data)) {
      const container = document.getElementById(id);
      if (container) installContainer(container, descriptor, id === 'proof-network' ? pageProofDetails : {});
    }
    for (const button of document.querySelectorAll('[data-graph-expand]')) button.addEventListener('click', () => setExpanded(button, !button.closest('.graph-figure').classList.contains('graph-expanded')));
    const used = document.querySelector('[data-used-concepts-toggle]');
    if (used) used.addEventListener('click', () => {
      const list = document.getElementById(used.getAttribute('aria-controls')); if (!list) return;
      list.hidden = !list.hidden; used.setAttribute('aria-expanded', String(!list.hidden));
      used.textContent = `${list.hidden ? 'Show' : 'Hide'} referenced concepts`;
    });
    window.addEventListener('keydown', (event) => {
      if (!expandedFigure) return;
      if (event.key === 'Escape') {
        event.preventDefault();
        if (activeProofController?.selection) {
          const trigger = activeProofController.selectionTrigger;
          clearProofSelection(activeProofController);
          trigger?.focus?.();
          return;
        }
        const button = expandedFigure.querySelector('[data-graph-expand]'); setExpanded(button, false); button.focus();
      } else if (event.key === 'Tab') {
        const focusable = [...expandedFigure.querySelectorAll('button:not(:disabled), a[href], [tabindex="0"]')].filter((node) => node.getClientRects().length);
        const first = focusable[0], last = focusable.at(-1);
        if (event.shiftKey && document.activeElement === first) { event.preventDefault(); last?.focus(); }
        if (!event.shiftKey && document.activeElement === last) { event.preventDefault(); first?.focus(); }
      }
    });
    window.addEventListener('scroll', refreshGraphTooltip, { capture: true, passive: true });
    window.addEventListener('resize', refreshGraphTooltip, { passive: true });
    window.addEventListener('click', (event) => {
      const controller = activeProofController;
      if (!controller?.selection || !(event.target instanceof Element)) return;
      if (controller.panel?.contains(event.target) ||
          event.target.closest('[data-node-id], [data-edge-hit], .graph-zoom-controls')) return;
      clearProofSelection(controller);
    });
    document.documentElement.classList.add('graphs-interactive');
  }
  // Local preparation dispatches the same interaction install after its worker
  // has returned a complete validated drawing; public pages never load it.
  document.addEventListener('lax-graph-local-ready', (event) => {
    const container = document.getElementById(event.detail.id);
    if (container) installContainer(container, event.detail.data,
      container.id === 'proof-network' ? pageProofDetails : {});
  });
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', initialize); else initialize();
})();
