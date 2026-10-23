-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

-- Lax871432.DisjointUnionCounts
section
open Lax871432.HomomorphismCounts

namespace Lax871432.DisjointUnionCounts

/-- A homomorphism from a connected graph into a disjoint union maps into one of its two
parts. -/
axiom homCount_sum_right {U V W : Type*} [Finite U] [Finite V] [Finite W] (K : SimpleGraph U)
    (hK : K.Connected) (G₁ : SimpleGraph V) (G₂ : SimpleGraph W) :
    homCount K (G₁ ⊕g G₂) = homCount K G₁ + homCount K G₂

end Lax871432.DisjointUnionCounts
end
