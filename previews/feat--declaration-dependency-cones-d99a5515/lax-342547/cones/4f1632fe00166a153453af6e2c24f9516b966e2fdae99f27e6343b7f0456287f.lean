-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat

-- Lax342547.CliqueMinor
section
namespace Lax342547
end Lax342547

namespace Lax342547.CliqueMinor
end Lax342547.CliqueMinor
end

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

/-- The supremum of the cardinalities of pairwise touching matchings.
For finite vertex types, this supremum is attained. -/
noncomputable def connectedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), IsTouchingMatching G M ∧ M.card = n}

end Lax342547.ConnectedMatching
end

-- Lax342547.Counterexample
section
namespace Lax342547.Counterexample

open ConnectedMatching CliqueMinor

/-- Theorem 1.1, with the strict matching bound expressed in natural numbers. -/
axiom arbitrarily_large_small_connected_matching (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m

end Lax342547.Counterexample
end
