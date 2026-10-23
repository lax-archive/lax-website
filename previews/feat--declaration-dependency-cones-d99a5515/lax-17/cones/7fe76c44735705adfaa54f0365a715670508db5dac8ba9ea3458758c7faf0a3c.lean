-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite

-- Lax17.Degree
section
namespace Lax17
end Lax17

namespace Lax17.Degree
end Lax17.Degree
end

-- Lax17.Expansion
section
namespace Lax17.Expansion.BalancedSeparator
end Lax17.Expansion.BalancedSeparator

namespace Lax17.Expansion

universe u

open Lax17.Degree

/-- An unordered pair crosses the vertex set `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ x y : V, e = s(x, y) ∧
    ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S))

/-- The finite edge boundary of `S`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V)
    (fun e => e ∈ G.edgeSet ∧ Crosses S e)
    (Classical.decPred _)
    Finset.univ

/-- Every set of at most half the vertices expands by a factor of `a / b`. -/
def IsEdgeExpander {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧
    ∀ S : Finset V, 0 < S.card → 2 * S.card ≤ Fintype.card V →
      b * (edgeBoundary G S).card ≥ a * S.card

namespace MatchingRound

end MatchingRound

namespace CutMatchingTranscript

end CutMatchingTranscript

end Lax17.Expansion
end
