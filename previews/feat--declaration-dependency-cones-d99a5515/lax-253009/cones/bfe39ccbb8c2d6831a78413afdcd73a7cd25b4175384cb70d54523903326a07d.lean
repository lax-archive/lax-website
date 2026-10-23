-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
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

end Lax253009.HigherMoments
end

-- Lax253009.BooleanFourier
section
namespace Lax253009
end Lax253009

namespace Lax253009.BooleanFourier
end Lax253009.BooleanFourier
end

-- Lax253009.Hypercontractivity
section
namespace Lax253009.Hypercontractivity
end Lax253009.Hypercontractivity
end

-- Lax253009.DoubleCoverBounds
section
namespace Lax253009.DoubleCoverBounds

open HigherMoments

open scoped BigOperators

noncomputable def weight {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (m : ℕ) : ℝ := by
  classical
  exact ∑ S : Fin m → Finset ι, if DoubleCover S then ∏ j, c (S j) else 0

end Lax253009.DoubleCoverBounds
end
