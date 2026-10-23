-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique

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
