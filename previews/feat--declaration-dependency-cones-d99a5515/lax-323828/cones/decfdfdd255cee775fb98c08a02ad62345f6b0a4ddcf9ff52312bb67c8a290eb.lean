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

open scoped Classical

open HigherMoments

open scoped BigOperators

/-- Sum the products of coefficients over tuples in which every used coordinate occurs at least twice. -/
noncomputable def weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) : ℝ :=
  ∑ S : Fin m → Finset ι, if DoubleCover S then ∏ j, c (S j) else 0

end Lax323828.DoubleCoverBounds
end
