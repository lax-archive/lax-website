import { esc } from "../html.js";
import { highlightSnippet } from "../highlight.js";

// The concept/proof card originally published in codex/landing-concept-proof-flip.
const CONCEPT_DEMO = String.raw`import Mathlib.Combinatorics.SimpleGraph.Clique

open Filter Real SimpleGraph

abbrev C₅ : SimpleGraph (Fin 5) := cycleGraph 5

def C₅Free {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ ∃ f : Fin 5 ↪ V, C₅ = G.comap f

def HasLargeHomogeneousSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℝ) : Prop :=
  G.indepNum ≥ r ∨ G.cliqueNum ≥ r

axiom erdosHajnal_C₅ :
  ∃ c > 0, ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    C₅Free G → HasLargeHomogeneousSet G ((n : ℝ) ^ c)`;

const PROOF_DEMO = String.raw`theorem erdosHajnal_C₅ :
    ∃ c > 0,
      ∀ᶠ n in atTop,
        ∀ G : SimpleGraph (Fin n),
          C₅Free G →
            HasLargeHomogeneousSet G ((n : ℝ) ^ c) := by
  obtain ⟨c, hc, hmain⟩ :=
    polynomial_homogeneous_set_for_five_hole
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmain] with n hn
  intro G hG
  exact hn G (by
    simpa [C₅Free] using hG)`;

function landingDemoFace(
  side: "concept" | "proof",
  path: string,
  code: string,
): string {
  const concept = side === "concept";
  const codeBlock = concept
    ? `<span class="landing-demo-code"><code>${code}</code></span>`
    : `<span class="landing-demo-code landing-demo-code-excerpt">
<span class="landing-demo-continuation" aria-hidden="true"><i></i><b>⋮</b><i></i></span>
<code>${code}</code>
<span class="landing-demo-continuation" aria-hidden="true"><i></i><b>⋮</b><i></i></span>
</span>`;
  return `<span class="landing-demo-face landing-demo-${side}" aria-hidden="true">
<span class="landing-demo-filebar">
<span class="landing-demo-file-heading"><strong>${concept ? "Concept file" : "Proof file"}</strong>${concept ? "" : '<span class="landing-demo-file-note">excerpt</span>'}</span>
<span class="landing-demo-file-path">${esc(path)}</span>
</span>
${codeBlock}
<span class="landing-demo-trust">
<span class="landing-demo-trust-copy"><strong>${concept ? "Meaning" : "Evidence"}</strong><small>${concept ? "read by people" : "checked by Lean"}</small></span>
${concept ? '<span class="landing-demo-turn"><span>See the proof</span><b>↻</b></span>' : ""}
</span>
</span>`;
}

export async function proofFlipDemo(): Promise<string> {
  const [concept, proof] = await Promise.all([
    highlightSnippet(CONCEPT_DEMO, { accentLines: [14, 15, 16] }),
    highlightSnippet(PROOF_DEMO, { startLine: 417 }),
  ]);
  return `<figure class="proof-flip-figure">
<button class="landing-demo-card" type="button" data-proof-flip aria-pressed="false" aria-label="Concept file: Erdős–Hajnal for the five-cycle. Hover or activate to see a proof excerpt.">
<span class="landing-demo-inner">
${landingDemoFace("concept", "concepts/ErdosHajnal/C5.lean", concept)}
${landingDemoFace("proof", "proofs/ErdosHajnalProofs/C5.lean", proof)}
</span>
</button>
<figcaption>
<span data-proof-flip-concept-caption>Concepts to review and endorse on the website</span>
<span data-proof-flip-proof-caption hidden>Proofs available in the submitter's git repository</span>
</figcaption>
</figure>`;
}
