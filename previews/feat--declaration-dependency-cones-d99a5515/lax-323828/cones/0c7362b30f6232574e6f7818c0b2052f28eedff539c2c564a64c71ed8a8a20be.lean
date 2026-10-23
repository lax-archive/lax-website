-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax323828.ProductMoments
section
namespace Lax323828
end Lax323828

namespace Lax323828.ProductMoments
end Lax323828.ProductMoments
end

-- Lax323828.HigherMoments
section
namespace Lax323828.HigherMoments

open scoped BigOperators

def DoubleCover {ι α : Type} [DecidableEq ι] [Fintype α] (S : α → Finset ι) : Prop :=
  ∀ i ∈ Finset.univ.biUnion S, 2 ≤ (Finset.univ.filter fun j ↦ i ∈ S j).card

end Lax323828.HigherMoments
end

-- Lax323828.BooleanFourier
section
namespace Lax323828
end Lax323828

namespace Lax323828.BooleanFourier
end Lax323828.BooleanFourier
end

-- Lax323828.Hypercontractivity
section
namespace Lax323828.Hypercontractivity
end Lax323828.Hypercontractivity
end

-- Lax323828.DoubleCoverBounds
section
namespace Lax323828.DoubleCoverBounds
end Lax323828.DoubleCoverBounds
end

-- Lax323828.SmallUnionDoubleCovers
section
namespace Lax323828.SmallUnionDoubleCovers

open scoped Classical

open HigherMoments

open scoped BigOperators

/-- The total product weight of double-cover tuples whose union has exactly `t` coordinates. -/
noncomputable def weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m t : ℕ) : ℝ :=
  ∑ S : Fin m → Finset ι,
    if DoubleCover S ∧ (Finset.univ.biUnion S).card = t then ∏ j, c (S j) else 0

axiom bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l m t : ℕ) (δ : ℝ)
    (hc : ∀ S, 0 ≤ c S) (hsmall : ∀ S, c S ≤ δ) (hδ : 0 ≤ δ)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hmt : 2 * t ≤ m) :
  weight c m t ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))

end Lax323828.SmallUnionDoubleCovers
end
