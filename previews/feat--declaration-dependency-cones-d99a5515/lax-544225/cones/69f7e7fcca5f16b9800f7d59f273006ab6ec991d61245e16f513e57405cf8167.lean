-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Defs.PartialOrder

-- Lax544225.Semimetric
section
universe u

namespace Lax544225.Semimetric

open scoped NNReal

/-- A nonnegative real-valued distance on a carrier. -/
abbrev Distance (S : Type u) := S → S → ℝ≥0

end Lax544225.Semimetric
end

-- Lax544225.OrderedSemimetric
section
namespace Lax544225.OrderedSemimetric
end Lax544225.OrderedSemimetric
end

-- Lax544225.SumProductSpace
section
universe u

namespace Lax544225.SumProductSpace

open Semimetric OrderedSemimetric

open scoped BigOperators

/-- Sum of the base distances between corresponding coordinates. -/
noncomputable def sumDistance {S : Type u} (d : Distance S) (n : ℕ) : Distance (Fin n → S) :=
  fun f g => ∑ i, d (f i) (g i)

end Lax544225.SumProductSpace
end
