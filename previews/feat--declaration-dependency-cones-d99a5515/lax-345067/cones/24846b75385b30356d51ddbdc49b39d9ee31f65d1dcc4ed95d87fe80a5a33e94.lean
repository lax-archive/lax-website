-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

-- Lax345067.Ramsey
section
namespace Lax345067.Ramsey

/-- Ramsey's theorem: a large enough graph contains a clique on `a`
vertices or an independent set on `b` vertices. -/
axiom exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard)

end Lax345067.Ramsey
end
