-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin

-- Lax342547.ConnectedMatching
section
namespace Lax342547.ConnectedMatching

universe u

variable {V : Type u}

/-- A finite matching whose edges are pairwise touching: each member is a
two-vertex clique, and distinct members are disjoint and joined by an edge. -/
def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

end Lax342547.ConnectedMatching
end

-- Lax342547.SampledGraph
section
namespace Lax342547
end Lax342547

namespace Lax342547.SampledGraph
end Lax342547.SampledGraph
end

-- Lax342547.MatchingSamples
section
namespace Lax342547.MatchingSamples

open Lax342547.ConnectedMatching Lax342547.SampledGraph

noncomputable def oriented {V : Type} (e : Finset V) (he : e.card = 2) : Bool → V :=
  fun b => ((e.equivFinOfCardEq he).symm (if b then 1 else 0)).val

axiom matching_orientation_injective {V : Type} (G : SimpleGraph V) (M : Finset (Finset V))
    (hM : IsTouchingMatching G M) :
    Function.Injective (fun eb : M × Bool => oriented eb.1.val (hM.1 _ eb.1.property).1 eb.2)

end Lax342547.MatchingSamples
end
