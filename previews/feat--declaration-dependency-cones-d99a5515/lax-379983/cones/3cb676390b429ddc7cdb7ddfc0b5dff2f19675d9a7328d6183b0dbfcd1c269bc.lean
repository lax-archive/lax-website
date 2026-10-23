-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax379983.FeedbackEdgeNumber
section
namespace Lax379983.FeedbackEdgeNumber

/-- The minimum number of edges whose deletion makes the graph acyclic. -/
noncomputable def feedbackEdgeNumber {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Set (Sym2 V),
    F ⊆ G.edgeSet ∧ F.ncard = n ∧ (G.deleteEdges F).IsAcyclic}

end Lax379983.FeedbackEdgeNumber
end
