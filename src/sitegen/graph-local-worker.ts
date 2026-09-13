/** Separately packaged local-preview entry. Public archive pages never load
 * this module or any of its dependencies. Measurements come from the local
 * browser; layout and final SVG validation use exactly the archive core. */
import { layoutGraph } from "../graph-layout/index.js";
import { canonicalJson } from "../graph-layout/normalize.js";
import type { LayoutProfile } from "../graph-layout/types.js";
import { measureDisplayGraph } from "./graph-node-size.js";
import { graphInteractionPayload, graphSvg } from "./graph-svg.js";
import type { DisplayGraph, GraphLabel } from "./graph-project.js";

interface LocalContainer {
  initial: string; ancestors: number; descendants: number;
  views: Record<string, { display: DisplayGraph; status: string }>;
}
interface Work {
  labels: readonly (GraphLabel & { text: string; signature: string })[];
  containers: Record<string, LocalContainer>; profile: LayoutProfile;
}
const worker = globalThis as unknown as {
  onmessage: ((event: { data: Work }) => void) | null;
  postMessage: (message: unknown) => void;
};
async function digest(value: string): Promise<string> {
  return [...new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(value)))].map((n) => n.toString(16).padStart(2, "0")).join("");
}
worker.onmessage = (event) => {
  void (async () => {
    const labels = new Map(event.data.labels.map((label) => [label.text, label])), profile = event.data.profile;
    for (const [id, container] of Object.entries(event.data.containers)) {
      const views: Record<string, { svg: string; interaction: ReturnType<typeof graphInteractionPayload>; height: number; status: string }> = {};
      for (const [state, view] of Object.entries(container.views)) {
        const measured = measureDisplayGraph(view.display, labels, profile.portSeparation);
        const inputDigest = await digest(canonicalJson({ graph: measured.graph, labels: [...labels], view: view.display, profile }));
        const result = layoutGraph(measured.graph, { inputDigest, profile });
        views[state] = { svg: graphSvg(measured, result.geometry, `${id}-${state}`),
          interaction: graphInteractionPayload(measured), height: result.geometry.bounds.height, status: view.status };
      }
      worker.postMessage({ id, data: { initial: container.initial, ancestors: container.ancestors, descendants: container.descendants, views } });
    }
    worker.postMessage({ complete: true });
  })().catch((error: unknown) => worker.postMessage({ error: error instanceof Error ? error.message : String(error) }));
};
