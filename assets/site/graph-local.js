/* Fresh local-preview labels only. Ordinary archive HTML never references
 * this script, the measurement helper, or the separately packaged worker. */
(() => {
  'use strict';
  const assetBase = new URL('.', document.currentScript.src);
  async function prepare() {
    const local = JSON.parse(document.getElementById('graph-data')?.textContent || '{}').local;
    if (!local) return;
    const containers = Object.keys(local.containers).map((id) => document.getElementById(id)).filter(Boolean);
    const status = (text) => {
      for (const container of containers) {
        const message = document.createElement('p');
        message.className = 'graph-local-status'; message.setAttribute('role', 'status'); message.textContent = text;
        container.replaceChildren(message);
      }
    };
    try {
      if (location.protocol === 'file:') throw new Error('Open this local preview with lax serve. For a file export, build with --self-contained-graphs and measured labels.');
      status('Preparing the local graph…');
      const labels = await globalThis.laxGraphMeasure.measureLabels(local.requests,
        { ...local.environment, assetBaseUrl: assetBase.href }, { local: true });
      const worker = new Worker(new URL('graph-local/sitegen/graph-local-worker.js', assetBase), { type: 'module' });
      worker.onmessage = (event) => {
        if (event.data.error) { status(event.data.error); worker.terminate(); return; }
        if (event.data.complete) { worker.terminate(); return; }
        const { id, data } = event.data, container = document.getElementById(id);
        if (!container) return;
        const initial = data.views[data.initial];
        container.innerHTML = initial.svg;
        container.style.height = `${Math.min(initial.height, 720)}px`;
        document.dispatchEvent(new CustomEvent('lax-graph-local-ready', { detail: { id, data } }));
      };
      worker.onerror = (error) => { status(`Local graph preparation failed: ${error.message}`); worker.terminate(); };
      worker.postMessage({ containers: local.containers, labels, profile: local.profile });
    } catch (error) { status(error.message); }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', prepare); else prepare();
})();
