-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.SetTheory.Cardinal.Finite

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.CoproductCounts
section
open Lax871432.HomomorphismCounts

namespace Lax871432.CoproductCounts

/-- A homomorphism from a disjoint union is a pair of homomorphisms from its two parts. -/
axiom homCount_sum_left {U V W : Type*} [Finite U] [Finite V] [Finite W] (F₁ : SimpleGraph U)
    (F₂ : SimpleGraph V) (G : SimpleGraph W) :
    homCount (F₁ ⊕g F₂) G = homCount F₁ G * homCount F₂ G

end Lax871432.CoproductCounts
end
