// Shared polygon operations for the two paper views, in display pixels.
(() => {
  // Inset the orthogonal passage outline so adjacent declarations leave a
  // small unshaded gap, including when their boundary is inside one line.
  function inset(points, padding = 1) {
    const clean = points.filter(([x, y], i) => {
      const prev = points[(i + points.length - 1) % points.length];
      return x !== prev[0] || y !== prev[1];
    });
    // An end marker at the start of a line can leave a zero-width tail;
    // likewise a begin marker at the line's far edge. Remove collinear
    // vertices (including those retraced tails) before offsetting edges.
    for (let i = 0; clean.length >= 3 && i < clean.length;) {
      const prev = clean[(i + clean.length - 1) % clean.length];
      const point = clean[i];
      const next = clean[(i + 1) % clean.length];
      const cross = (point[0] - prev[0]) * (next[1] - point[1]) - (point[1] - prev[1]) * (next[0] - point[0]);
      if (Math.abs(cross) < 0.000001) { clean.splice(i, 1); i = 0; }
      else i++;
    }
    if (clean.length < 3) return [];
    const edges = clean.map(([x, y], i) => {
      const next = clean[(i + 1) % clean.length];
      return [next[0] - x, next[1] - y];
    });
    const lengths = edges.map(([x, y]) => Math.hypot(x, y));
    const area = clean.reduce((sum, [x, y], i) => {
      const next = clean[(i + 1) % clean.length];
      return sum + x * next[1] - y * next[0];
    }, 0);
    if (Math.abs(area) < 0.001) return [];
    const distance = Math.min(padding, ...lengths.map((length) => length / 4));
    const normals = edges.map(([x, y], i) => [-y / lengths[i] * Math.sign(area), x / lengths[i] * Math.sign(area)]);
    return clean.map(([x, y], i) => {
      const prev = normals[(i + clean.length - 1) % clean.length];
      const next = normals[i];
      const denominator = 1 + prev[0] * next[0] + prev[1] * next[1];
      if (denominator < 0.001) return [x, y];
      return [x + distance * (prev[0] + next[0]) / denominator, y + distance * (prev[1] + next[1]) / denominator];
    });
  }

  function contains(points, x, y) {
    let inside = false;
    for (let i = 0, j = points.length - 1; i < points.length; j = i++) {
      const [xi, yi] = points[i];
      const [xj, yj] = points[j];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  }

  globalThis.laxManuscriptRegions = { inset, contains };
})();
