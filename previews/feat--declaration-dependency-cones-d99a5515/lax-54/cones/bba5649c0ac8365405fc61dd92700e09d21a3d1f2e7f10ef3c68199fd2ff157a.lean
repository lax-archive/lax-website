-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54
end Lax54

namespace Lax54.GraphDefinitions
end Lax54.GraphDefinitions

namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb
end

-- Lax54.AveragingLemma
section
namespace Lax54.AveragingLemma

open Lax54.GraphDefinitions

universe u

/-- Lemma 4.2, with all inequalities written over the natural numbers. -/
axiom sparse_graph_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (Z : Finset V) (E m : ℕ),
      0 < E → 2 * m ≤ Z.card + 1 →
      E * 2 * (G.induce (Z : Set V)).edgeFinset.card ≤
        Z.card * (Z.card - 1) →
      ∃ X : Finset V, X ⊆ Z ∧ X.card = m ∧
        ∀ x : {v : V // v ∈ X},
          E * (G.induce (X : Set V)).degree x ≤ 4 * (m - 1)

end Lax54.AveragingLemma
end
