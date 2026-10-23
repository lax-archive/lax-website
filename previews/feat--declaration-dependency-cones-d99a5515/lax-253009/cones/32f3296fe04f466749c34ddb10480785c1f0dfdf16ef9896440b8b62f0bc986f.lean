-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.ProductMoments
section
namespace Lax253009
end Lax253009

namespace Lax253009.ProductMoments
end Lax253009.ProductMoments
end

-- Lax253009.HigherMoments
section
namespace Lax253009.HigherMoments

open scoped BigOperators

def DoubleCover {ι α : Type} [DecidableEq ι] [Fintype α] (S : α → Finset ι) : Prop :=
  ∀ i ∈ Finset.univ.biUnion S, 2 ≤ (Finset.univ.filter fun j ↦ i ∈ S j).card

axiom double_subcover {ι : Type} [DecidableEq ι] {m : ℕ}
    (S : Fin m → Finset ι) (hS : DoubleCover S) (r : ℕ)
    (hr : 2 * (Finset.univ.biUnion S).card ≤ r) (hrm : r ≤ m) :
  ∃ J : Finset (Fin m), J.card = r ∧
    ∀ i ∈ Finset.univ.biUnion S, 2 ≤ (J.filter fun j ↦ i ∈ S j).card

end Lax253009.HigherMoments
end
