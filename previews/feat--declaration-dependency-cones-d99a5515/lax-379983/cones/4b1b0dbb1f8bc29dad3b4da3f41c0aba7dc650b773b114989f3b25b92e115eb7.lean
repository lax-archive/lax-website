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

-- Lax379983.FeedbackVertexNumber
section
namespace Lax379983.FeedbackVertexNumber

/-- The minimum number of vertices whose deletion makes the graph acyclic. -/
noncomputable def feedbackVertexNumber {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ S : Set V, S.ncard = n ∧ (G.induce Sᶜ).IsAcyclic}

end Lax379983.FeedbackVertexNumber
end

-- Lax379983.FeedbackNumberComparison
section
namespace Lax379983.FeedbackNumberComparison

open Lax379983.FeedbackVertexNumber Lax379983.FeedbackEdgeNumber

/-- Every finite simple graph has feedback vertex number at most its feedback edge number. -/
axiom feedbackVertexNumber_le_feedbackEdgeNumber {V : Type*} [Finite V]
    (G : SimpleGraph V) : feedbackVertexNumber G ≤ feedbackEdgeNumber G

end Lax379983.FeedbackNumberComparison
end
