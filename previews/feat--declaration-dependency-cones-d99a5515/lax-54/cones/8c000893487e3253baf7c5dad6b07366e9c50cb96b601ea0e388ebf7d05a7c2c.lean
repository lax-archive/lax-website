-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb

open Finset

open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/--
The maximum-degree version of the sparse-side conclusion. The witness `X`
satisfies `|V(G)| ≤ D|X|`; in either `G[X]` or its complement, every degree
`d(x)` satisfies `E d(x) < |X|`.
-/
def HasLowDegreeSide {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E D : ℕ) : Prop :=
  ∃ X : Finset V,
    Fintype.card V ≤ D * X.card ∧
      ((∀ x : {v : V // v ∈ X},
          E * (G.induce (X : Set V)).degree x < X.card) ∨
       (∀ x : {v : V // v ∈ X},
          E * (Gᶜ.induce (X : Set V)).degree x < X.card))

end Lax54.GraphDefinitions
end

-- Lax54.MaximumDegreeReduction
section
namespace Lax54.MaximumDegreeReduction

open Lax54.GraphDefinitions

open scoped SimpleGraph

universe u v

/-- The maximum-degree form of Rödl's theorem used in Section 4. -/
axiom maximum_degree_reduction :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) (E : ℕ),
      0 < E → ∃ D : ℕ, 0 < D ∧
        ∀ {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          ¬ H ⊴ G → HasLowDegreeSide G E D

end Lax54.MaximumDegreeReduction
end
