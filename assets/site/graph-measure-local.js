/* First-party SVG text measurement. Used verbatim by the archive build host
 * and the separate local-preview path; ordinary archive pages never load it.
 * There is deliberately no graph/layout code in this file. */
(function (scope) {
  'use strict';
  const VERSION = 'svg-labels-2';
  const FAMILY = "'Latin Modern', 'Latin Modern Math', 'Lax Graph Fallback'";
  const scriptBase = typeof document !== 'undefined' && document.currentScript
    ? new URL('.', document.currentScript.src).href : undefined;
  const loaded = new Map();

  function normalize(request) {
    const result = {
      text: request.text, maxWidth: request.maxWidth,
      fontSize: request.fontSize ?? 12, fontWeight: request.fontWeight ?? 400,
      letterSpacing: request.letterSpacing ?? 0, lineHeight: request.lineHeight ?? 16,
    };
    if (typeof result.text !== 'string' || !Number.isFinite(result.maxWidth) || result.maxWidth <= 0 ||
        !Number.isFinite(result.fontSize) || result.fontSize <= 0 ||
        ![400, 700].includes(result.fontWeight) || !Number.isFinite(result.letterSpacing) ||
        result.letterSpacing < 0 || !Number.isFinite(result.lineHeight) || result.lineHeight <= 0) {
      throw new Error('GRAPH_LABEL_REQUEST: invalid text, dimensions or font style');
    }
    return result;
  }

  function covered(code, ranges) {
    let lo = 0, hi = ranges.length;
    while (lo < hi) {
      const middle = (lo + hi) >>> 1, range = ranges[middle];
      if (code < range[0]) hi = middle;
      else if (code > range[1]) lo = middle + 1;
      else return true;
    }
    return false;
  }

  function assertCoverage(request, environment) {
    const fonts = environment.fontFaces.filter((face) =>
      face.family !== 'Latin Modern' || face.weight === request.fontWeight);
    const missing = new Set();
    for (const char of request.text) {
      // These are the only characters normalized away by the SVG wrapping
      // rules. Other controls and unsupported glyphs produce a diagnostic.
      if (/^[\t\n\r ]$/u.test(char)) continue;
      const code = char.codePointAt(0);
      if (!fonts.some((font) => covered(code, font.coverage))) missing.add(code);
    }
    if (missing.size) throw new Error('GRAPH_LABEL_GLYPH_UNSUPPORTED: bundled graph fonts lack ' +
      [...missing].sort((a, b) => a - b).map((code) => 'U+' + code.toString(16).toUpperCase().padStart(4, '0')).join(', '));
  }

  function keyData(request, signature) {
    return JSON.stringify([signature, request.text, request.maxWidth, request.fontSize,
      request.fontWeight, request.letterSpacing, request.lineHeight]);
  }

  async function digest(value) {
    if (!scope.crypto || !scope.crypto.subtle) {
      throw new Error('GRAPH_MEASUREMENT_CRYPTO: exact local measurement needs a secure local origin or a self-contained file export');
    }
    const bytes = await scope.crypto.subtle.digest('SHA-256', new TextEncoder().encode(value));
    return Array.from(new Uint8Array(bytes), (b) => b.toString(16).padStart(2, '0')).join('');
  }

  async function loadFonts(environment) {
    if (!loaded.has(environment.fontSignature)) loaded.set(environment.fontSignature, (async () => {
      const base = environment.assetBaseUrl || scriptBase;
      if (!base) throw new Error('GRAPH_FONT_URL: local measurement needs its packaged asset URL');
      await Promise.all(environment.fontFaces.map(async (face) => {
        const url = face.url || new URL(face.file, base).href;
        const font = new FontFace(face.family, 'url(' + JSON.stringify(url) + ')', {
          style: 'normal', weight: String(face.weight), display: 'block',
        });
        try { await font.load(); }
        catch { throw new Error('GRAPH_FONT_LOAD: could not load ' + face.file); }
        document.fonts.add(font);
      }));
      await document.fonts.ready;
    })());
    await loaded.get(environment.fontSignature);
  }

  function styledText(request) {
    const namespace = 'http://www.w3.org/2000/svg';
    const text = document.createElementNS(namespace, 'text');
    text.setAttribute('font-family', FAMILY);
    text.setAttribute('font-size', String(request.fontSize));
    text.setAttribute('font-weight', String(request.fontWeight));
    text.setAttribute('letter-spacing', String(request.letterSpacing));
    text.setAttribute('text-anchor', 'start');
    text.setAttribute('dominant-baseline', 'auto');
    text.setAttribute('font-kerning', 'normal');
    text.setAttribute('text-rendering', 'geometricPrecision');
    text.style.fontKerning = 'normal';
    text.style.lineHeight = String(request.lineHeight) + 'px';
    text.style.fontSynthesis = 'none';
    text.style.setProperty('-webkit-font-smoothing', 'antialiased');
    text.style.whiteSpace = 'pre';
    text.setAttribute('xml:space', 'preserve');
    return text;
  }

  function measureOne(request, svg) {
    const namespace = 'http://www.w3.org/2000/svg';
    const text = styledText(request);
    svg.appendChild(text);
    const probe = document.createElementNS(namespace, 'tspan');
    probe.setAttribute('x', '0');
    probe.setAttribute('y', '0');
    text.appendChild(probe);
    const measurements = new Map();
    function measure(value) {
      let metric = measurements.get(value);
      if (metric) return metric;
      probe.textContent = value;
      // Both logical advance and glyph overhang contribute to the envelope.
      const advance = probe.getComputedTextLength();
      const box = probe.getBBox();
      metric = { x: box.x, y: box.y, width: box.width, height: box.height, advance };
      measurements.set(value, metric);
      return metric;
    }
    function width(value) {
      const metric = measure(value);
      return Math.max(metric.advance, metric.x + metric.width) - Math.min(0, metric.x);
    }
    const graphemes = new Intl.Segmenter('en', { granularity: 'grapheme' });
    function wrap(maxWidth) {
      const lines = [];
      for (const paragraph of request.text.replace(/\r\n?/gu, '\n').split('\n')) {
        const words = paragraph.replace(/\t/gu, ' ').trim().split(/ +/u).filter(Boolean);
        let current = '';
        if (!words.length) { lines.push(''); continue; }
        for (const word of words) {
          const next = current ? current + ' ' + word : word;
          if (width(next) <= maxWidth) { current = next; continue; }
          if (current) { lines.push(current); current = ''; }
          if (width(word) <= maxWidth) { current = word; continue; }
          // Never truncate an identifier or split a combining cluster. Every
          // accepted prefix is measured in SVG; no code-point width estimate.
          for (const entry of graphemes.segment(word)) {
            const nextPart = current + entry.segment;
            if (width(nextPart) <= maxWidth) { current = nextPart; continue; }
            if (current) { lines.push(current); current = ''; }
            if (width(entry.segment) > maxWidth) {
              throw new Error('GRAPH_LABEL_WIDTH: a grapheme exceeds the requested label width');
            }
            current = entry.segment;
          }
        }
        lines.push(current);
      }
      return lines;
    }
    const sample = measure('Hg');
    const assembled = text.cloneNode(false);
    svg.appendChild(assembled);
    let lines, raw, minX, totalWidth, wholeInk, wrapWidth = request.maxWidth;
    // Browser shaping and fallback ink envelopes can depend on the complete
    // text element. A sole-tspan probe is useful for greedy proposals, but its
    // isolated glyph box is not the emitted multiline result.
    const refinementLimit = Array.from(request.text).length + 1;
    for (let refinement = 0; ; refinement++) {
      lines = wrap(wrapWidth);
      const spans = lines.map((line, index) => {
        const span = document.createElementNS(namespace, 'tspan');
        span.setAttribute('x', '0'); span.setAttribute('y', String(index * request.lineHeight));
        span.textContent = line;
        return span;
      });
      assembled.replaceChildren(...spans);
      wholeInk = assembled.getBBox();
      raw = spans.map((span, index) => {
        const advance = span.getComputedTextLength(), box = span.getBBox();
        return { x: box.x, y: box.y - index * request.lineHeight, width: box.width,
          height: box.height, advance };
      });
      minX = Math.min(0, wholeInk.x, ...raw.map((box) => box.x));
      totalWidth = Math.max(0, wholeInk.x + wholeInk.width, ...raw.map((box) => Math.max(box.advance, box.x + box.width))) - minX;
      if (totalWidth <= request.maxWidth) break;
      // Tighten only after measuring an assembled overflow, and verify the
      // complete replacement. Work is bounded by the input length; failure
      // is explicit rather than accepting clipping or dropping characters.
      if (refinement >= refinementLimit) {
        throw new Error('GRAPH_LABEL_WIDTH: assembled text wrapping exceeded its refinement budget');
      }
      wrapWidth -= Math.max(totalWidth - request.maxWidth, 1 / 64);
      if (wrapWidth <= 0) throw new Error('GRAPH_LABEL_WIDTH: assembled text cannot fit the requested width');
    }
    const referenceTop = sample.y - Math.max(0, request.lineHeight - sample.height) / 2;
    const top = Math.min(referenceTop, wholeInk.y, ...raw.map((box, index) => index * request.lineHeight + box.y));
    const bottom = Math.max(referenceTop + lines.length * request.lineHeight, wholeInk.y + wholeInk.height,
      ...raw.map((box, index) => index * request.lineHeight + box.y + box.height));
    const result = {
      text: request.text, width: totalWidth, height: bottom - top,
      lines: lines.map((line, index) => ({
        text: line, x: -minX, y: index * request.lineHeight - top,
        ink: { x: raw[index].x - minX, y: index * request.lineHeight + raw[index].y - top,
          width: raw[index].width, height: raw[index].height },
      })),
    };
    assembled.remove(); text.remove();
    return result;
  }

  async function measureLabels(input, environment, options) {
    const requests = input.map(normalize);
    for (const request of requests) assertCoverage(request, environment);
    await loadFonts(environment);
    // Local geometry is never mistaken for a result from the pinned archive
    // host. It can use the user's browser without adding an npm dependency.
    const signature = options && options.local
      ? await digest(JSON.stringify([environment.signature, 'local-browser', navigator.userAgent]))
      : environment.signature;
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('width', '1');
    svg.setAttribute('height', '1');
    svg.setAttribute('aria-hidden', 'true');
    svg.style.position = 'absolute';
    // Hidden, clipped probes do not alter local preview scroll extents.
    svg.style.left = '0';
    svg.style.top = '0';
    svg.style.visibility = 'hidden';
    svg.style.overflow = 'hidden';
    document.body.appendChild(svg);
    try {
      // Stylesheet-connected faces can still be unloaded after the explicit
      // FontFace objects above finish. Insert actual styled text first, then
      // load every matching CSS face and await the resulting layout/font
      // work. Early fallback advances are never accepted as final metrics.
      const seeds = requests.map((request) => {
        const text = styledText(request);
        text.textContent = request.text || 'Hg';
        svg.appendChild(text);
        text.getComputedTextLength();
        return text;
      });
      const glyphs = requests.map((request) => request.text).join('') || 'Hg';
      await Promise.all(environment.fontFaces.map(async (face) => {
        try { await document.fonts.load(String(face.weight) + ' 12px ' + JSON.stringify(face.family), glyphs); }
        catch { throw new Error('GRAPH_FONT_LOAD: could not load stylesheet face ' + face.family); }
      }));
      await document.fonts.ready;
      for (const seed of seeds) seed.remove();
      const measured = requests.map((request) => measureOne(request, svg));
      return await Promise.all(measured.map(async (metric, index) => ({ ...metric,
        signature: await digest(keyData(requests[index], signature)),
      })));
    } finally { svg.remove(); }
  }

  scope.laxGraphMeasure = Object.freeze({ version: VERSION, fontFamily: FAMILY,
    normalize, assertCoverage, keyData, measureLabels });
})(globalThis);
