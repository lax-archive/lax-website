// Shared polygon operations for the two paper views, in display pixels.
(() => {
  const EPSILON = 0.001;

  function clean(points) {
    const out = points.filter(([x, y], i) => {
      const prev = points[(i + points.length - 1) % points.length];
      return x !== prev[0] || y !== prev[1];
    });
    // A marker at a line's edge can leave a retraced, zero-width tail.
    for (let i = 0; out.length >= 3 && i < out.length;) {
      const prev = out[(i + out.length - 1) % out.length];
      const point = out[i];
      const next = out[(i + 1) % out.length];
      const cross = (point[0] - prev[0]) * (next[1] - point[1]) - (point[1] - prev[1]) * (next[0] - point[0]);
      if (Math.abs(cross) < EPSILON) { out.splice(i, 1); i = 0; }
      else i++;
    }
    const area = out.reduce((sum, [x, y], i) => {
      const next = out[(i + 1) % out.length];
      return sum + x * next[1] - y * next[0];
    }, 0);
    if (Math.abs(area) < EPSILON) return [];
    return area < 0 ? out.reverse() : out;
  }

  // Scan the interiors, not their bounding boxes: adjacent passages can
  // share their first/last line without overlapping one another.
  function overlaps(a, b) {
    const ys = [...new Set([...a, ...b].map((point) => point[1]))].sort((x, y) => x - y);
    const crossings = (points, y) => points.flatMap(([x, py], i) => {
      const next = points[(i + 1) % points.length];
      return (py > y) !== (next[1] > y) ? [x] : [];
    }).sort((x, y) => x - y);
    for (let k = 1; k < ys.length; k++) {
      const y = (ys[k - 1] + ys[k]) / 2;
      const ax = crossings(a, y), bx = crossings(b, y);
      for (let i = 0; i < ax.length; i += 2) {
        for (let j = 0; j < bx.length; j += 2) {
          if (Math.min(ax[i + 1], bx[j + 1]) - Math.max(ax[i], bx[j]) > EPSILON) return true;
        }
      }
    }
    return false;
  }

  // Give the ink breathing room above/below and beyond the left margin.
  // Facing edges of disjoint declarations share the available space,
  // always reserving a small gap; intentionally overlapping marks do not.
  function prepare(outlines, gap = 1.5) {
    const shapes = outlines.map(({ points, left, right, group }) => {
      points = clean(points);
      const ys = [...new Set(points.map((point) => point[1]))].sort((a, b) => a - b);
      const stepPad = Math.min(3, ...ys.slice(1).map((y, i) => (y - ys[i]) / 4));
      const edges = points.map((a, i) => {
        const b = points[(i + 1) % points.length];
        const dx = b[0] - a[0], dy = b[1] - a[1];
        const length = Math.hypot(dx, dy);
        const normal = [dy / length, -dx / length];
        const pad = dy === 0 ? (a[1] === ys[0] || a[1] === ys[ys.length - 1] ? 3 : -stepPad)
          : Math.abs(a[0] - left) < EPSILON ? 4 : Math.abs(a[0] - right) < EPSILON ? 0 : 1.5;
        return { a, b, normal, pad };
      });
      return { points, edges, group };
    });
    for (let i = 0; i < shapes.length; i++) {
      for (let j = i + 1; j < shapes.length; j++) {
        const a = shapes[i], b = shapes[j];
        if (a.group !== b.group || overlaps(a.points, b.points)) continue;
        for (const ae of a.edges) for (const be of b.edges) {
          if (ae.normal[0] * be.normal[0] + ae.normal[1] * be.normal[1] > -0.999) continue;
          const axis = ae.normal[0] === 0 ? 0 : 1;
          if (Math.min(Math.max(ae.a[axis], ae.b[axis]), Math.max(be.a[axis], be.b[axis]))
            < Math.max(Math.min(ae.a[axis], ae.b[axis]), Math.min(be.a[axis], be.b[axis])) - EPSILON) continue;
          const distance = (be.a[0] - ae.a[0]) * ae.normal[0] + (be.a[1] - ae.a[1]) * ae.normal[1];
          if (distance < -EPSILON || ae.pad + be.pad <= distance - gap) continue;
          const room = distance - gap;
          if (ae.pad < room / 2) be.pad = room - ae.pad;
          else if (be.pad < room / 2) ae.pad = room - be.pad;
          else ae.pad = be.pad = room / 2;
        }
      }
    }
    return shapes.map(({ points, edges }) => clean(points.map(([x, y], i) => {
      const prev = edges[(i + edges.length - 1) % edges.length], next = edges[i];
      return [x + prev.normal[0] * prev.pad + next.normal[0] * next.pad,
        y + prev.normal[1] * prev.pad + next.normal[1] * next.pad];
    })));
  }

  // Only the edge actually touching the right margin can feed a ribbon.
  // A partial final line therefore never extends into the gutter.
  function rightEdge(points, right) {
    const index = points.findIndex(([x, y], i) => {
      const next = points[(i + 1) % points.length];
      return Math.abs(x - right) < EPSILON && Math.abs(next[0] - right) < EPSILON && next[1] > y;
    });
    return index < 0 ? null : { index, xl: right, top: points[index][1], bottom: points[(index + 1) % points.length][1] };
  }

  // A single line can join through empty space at its right. Only text in
  // the way calls for a narrow detour above the line. Add that detour to
  // the passage polygon at its top-right corner, then join its outer edge
  // to the card's full height with the same filled ribbon as every passage.
  function connection(points, margin, xr, ct, cb, line = null) {
    if (!points.length) return null;
    let edge = rightEdge(points, margin);
    if (!edge && line) {
      const right = Math.max(...points.map((p) => p[0]));
      const side = rightEdge(points, right);
      if (!side || right >= margin) return null;
      if (!line.blocked) {
        points = points.map(([x, y]) => [Math.abs(x - right) < EPSILON ? margin : x, y]);
      } else {
        const corner = points[side.index], prev = points[(side.index + points.length - 1) % points.length];
        const width = Math.min(2, (right - prev[0]) / 3);
        if (width <= 0) return null;
        let top = Math.min(corner[1] - 3, line.top - 3);
        if (Number.isFinite(line.previousBottom) && line.previousBottom < line.top - 2) {
          top = Math.max(top, (line.previousBottom + line.top - width) / 2);
        }
        const bottom = top + width;
        points = clean([
          ...points.slice(0, side.index),
          [right - width, corner[1]], [right - width, top], [margin, top],
          [margin, bottom], [right, bottom],
          ...points.slice(side.index + 1),
        ]);
      }
      edge = rightEdge(points, margin);
    }
    return edge ? { ...edge, points, xr, xm: (margin + xr) / 2, ct, cb } : null;
  }

  // One continuous path joins the rounded passage to its ribbon. There
  // is no separately antialiased edge at the text margin to leave a seam.
  function path(points, ribbon = null, radius = 6) {
    if (!points.length) return '';
    const corners = points.map((point, i) => {
      const prev = points[(i + points.length - 1) % points.length], next = points[(i + 1) % points.length];
      const before = Math.hypot(prev[0] - point[0], prev[1] - point[1]);
      const after = Math.hypot(next[0] - point[0], next[1] - point[1]);
      const r = ribbon && (i === ribbon.index || i === (ribbon.index + 1) % points.length)
        ? 0 : Math.min(radius, before / 2, after / 2);
      return { point, enter: point.map((v, axis) => v + (prev[axis] - v) * r / before),
        leave: point.map((v, axis) => v + (next[axis] - v) * r / after) };
    });
    const xy = (point) => point.map((v) => v.toFixed(2)).join(',');
    let d = `M${xy(corners[0].enter)}`;
    corners.forEach(({ point, leave }, i) => {
      d += `Q${xy(point)} ${xy(leave)}`;
      if (ribbon && i === ribbon.index) {
        const { xm, xr, top, bottom, ct, cb } = ribbon;
        d += `C${xy([xm, top])} ${xy([xm, ct])} ${xy([xr, ct])}L${xy([xr, cb])}C${xy([xm, cb])} ${xy([xm, bottom])} ${xy(corners[(i + 1) % corners.length].enter)}`;
      } else d += `L${xy(corners[(i + 1) % corners.length].enter)}`;
    });
    return `${d}Z`;
  }

  function contains(points, x, y) {
    let inside = false;
    for (let i = 0, j = points.length - 1; i < points.length; j = i++) {
      const [xi, yi] = points[i], [xj, yj] = points[j];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  globalThis.laxManuscriptRegions = { prepare, rightEdge, connection, path, contains };
})();
