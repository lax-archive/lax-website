// Public graph interaction only. Layout, routing, text sizing, and validation
// run before publication. No graph library or custom search engine is loaded.
(() => {
  'use strict';
  let activeGraphTooltip = null;
  let graphTooltipFrame;

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
    controller.svg = svg;
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
    const paint = () => {
      frame = null;
      const { x, y, scale } = controller.camera;
      cameraGroup.setAttribute('transform', `translate(${x},${y}) scale(${scale})`);
      if (scale !== paintedScale) { controller.fitScrollbars(); paintedScale = scale; }
      const output = container.closest('.graph-figure').querySelector('[data-graph-zoom-status]');
      if (output) output.value = `${Math.round(scale * 100)}%`;
      refreshGraphTooltip();
    };
    controller.paint = () => { if (!frame) frame = requestAnimationFrame(paint); };
    controller.restoreInline = (view) => {
      controller.autoFrame = false;
      controller.camera = { ...view.camera };
      paint();
      container.scrollLeft = view.left;
      container.scrollTop = view.top;
    };
    controller.frameExpanded = () => {
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
      controller.autoFrame = false;
      const camera = controller.camera;
      const scale = Math.max(0.2, Math.min(4, camera.scale * factor));
      const ratio = scale / camera.scale;
      const matrix = svg.getScreenCTM().inverse();
      const box = container.getBoundingClientRect();
      const at = new DOMPoint(clientPoint?.x ?? (box.left + box.width / 2), clientPoint?.y ?? (box.top + box.height / 2)).matrixTransform(matrix);
      camera.x = at.x - (at.x - camera.x) * ratio;
      camera.y = at.y - (at.y - camera.y) * ratio;
      camera.scale = scale; controller.paint();
    };
    controller.reset = () => {
      if (container.closest('.graph-figure').classList.contains('graph-expanded')) {
        controller.frameExpanded();
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
    let drag = null;
    svg.addEventListener('pointerdown', (event) => {
      // Native one-finger page/viewport scrolling remains available on touch.
      if (event.pointerType === 'touch' || event.button !== 0 || event.target.closest('a')) return;
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

  function installContainer(container, data) {
    const figure = container.closest('.graph-figure');
    data.views[data.initial].svg ||= container.querySelector('svg')?.outerHTML;
    const controller = { data, state: data.initial, request: 0 };
    controllers.set(container.id, controller);
    bindView(container, controller, data.views[data.initial].interaction);
    new ResizeObserver(() => {
      if (controller.autoFrame && figure.classList.contains('graph-expanded')) controller.frameExpanded();
      else controller.fitScrollbars();
    }).observe(container);
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
    let data;
    try { data = JSON.parse(raw?.textContent || '{}').prepared; } catch { return; }
    if (data) for (const [id, descriptor] of Object.entries(data)) {
      const container = document.getElementById(id);
      if (container) installContainer(container, descriptor);
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
        event.preventDefault(); const button = expandedFigure.querySelector('[data-graph-expand]'); setExpanded(button, false); button.focus();
      } else if (event.key === 'Tab') {
        const focusable = [...expandedFigure.querySelectorAll('button:not(:disabled), a[href], [tabindex="0"]')].filter((node) => node.getClientRects().length);
        const first = focusable[0], last = focusable.at(-1);
        if (event.shiftKey && document.activeElement === first) { event.preventDefault(); last?.focus(); }
        if (!event.shiftKey && document.activeElement === last) { event.preventDefault(); first?.focus(); }
      }
    });
    window.addEventListener('scroll', refreshGraphTooltip, { capture: true, passive: true });
    window.addEventListener('resize', refreshGraphTooltip, { passive: true });
    document.documentElement.classList.add('graphs-interactive');
  }
  // Local preparation dispatches the same interaction install after its worker
  // has returned a complete validated drawing; public pages never load it.
  document.addEventListener('lax-graph-local-ready', (event) => {
    const container = document.getElementById(event.detail.id);
    if (container) installContainer(container, event.detail.data);
  });
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', initialize); else initialize();
})();
