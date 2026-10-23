-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic

-- Lax544225.Semimetric
section
namespace Lax544225
end Lax544225

namespace Lax544225.Semimetric
end Lax544225.Semimetric
end

-- Lax544225.OrderedSemimetric
section
namespace Lax544225.OrderedSemimetric
end Lax544225.OrderedSemimetric
end

-- Lax544225.PrecisionGaps
section
universe u

namespace Lax544225.PrecisionGaps

open scoped NNReal

open Semimetric OrderedSemimetric

/-- The number of consecutive steps between the endpoints of a closed interval. -/
noncomputable def steps {S : Type u} [PartialOrder S] (x y : S) : ℕ :=
  (Set.Icc x y).ncard - 1

end Lax544225.PrecisionGaps
end
