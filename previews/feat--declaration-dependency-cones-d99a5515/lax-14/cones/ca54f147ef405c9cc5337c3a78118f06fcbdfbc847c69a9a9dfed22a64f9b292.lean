-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

-- Lax14.Ramsey
section
namespace Lax14.Ramsey

/-- Ramsey's theorem: a large enough graph contains a clique on `a`
vertices or an independent set on `b` vertices. -/
axiom exists_clique_or_indepSet (a b : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →
      (∃ S : Set (Fin n), G.IsClique S ∧ a ≤ S.ncard) ∨
      (∃ S : Set (Fin n), G.IsIndepSet S ∧ b ≤ S.ncard)

end Lax14.Ramsey
end
