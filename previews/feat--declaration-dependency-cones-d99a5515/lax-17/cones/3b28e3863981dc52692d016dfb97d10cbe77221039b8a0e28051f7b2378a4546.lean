-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs

-- Lax17.Degree
section
namespace Lax17
end Lax17

namespace Lax17.Degree
end Lax17.Degree
end

-- Lax17.SpanningTreeRounding
section
namespace Lax17.SpanningTreeRounding

universe u

open Finset

/-- Both endpoints of an unordered pair lie in `S`. -/
def PairInside {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  e.toFinset ⊆ S

/-- The finite edge set of `G`. -/
noncomputable def edges {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

/-- The edges of `G` with both endpoints in `S`. -/
noncomputable def internalEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V) (PairInside S) (Classical.decPred _) (edges G)

/-- The edges of `G` incident with `v`. -/
noncomputable def incidentEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (Sym2 V) :=
  (edges G).filter fun e => v ∈ e

/-- A feasible point of the bounded-degree spanning-tree relaxation. -/
structure FeasiblePoint {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ) where
  weight : Sym2 V → ℚ
  nonnegative : ∀ e : Sym2 V, e ∈ edges G → 0 ≤ weight e
  total :
    (edges G).sum weight = (Fintype.card V - 1 : ℕ)
  forest :
    ∀ S : Finset V, S ≠ Finset.univ →
      (internalEdges G S).sum weight ≤ (S.card - 1 : ℕ)
  degree :
    ∀ v : V, (incidentEdges G v).sum weight ≤ B

end Lax17.SpanningTreeRounding
end
