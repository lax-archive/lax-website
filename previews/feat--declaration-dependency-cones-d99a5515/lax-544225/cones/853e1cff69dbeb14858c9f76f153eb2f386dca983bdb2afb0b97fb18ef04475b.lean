-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.GetD
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Defs.PartialOrder

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

-- Lax544225.SumProductSpace
section
namespace Lax544225.SumProductSpace
end Lax544225.SumProductSpace
end

-- Lax544225.MaximumProductSpace
section
namespace Lax544225.MaximumProductSpace
end Lax544225.MaximumProductSpace
end

-- Lax544225.ListSpaces
section
universe u

namespace Lax544225.ListSpaces

open scoped NNReal

open Semimetric OrderedSemimetric

open scoped BigOperators

/-- Equal-length lists ordered coordinatewise; other lengths are incomparable. -/
def listLe {S : Type u} (le : S → S → Prop) (pad : S) (f g : List S) : Prop :=
  f.length = g.length ∧ ∀ i < f.length, le (f.getD i pad) (g.getD i pad)

end Lax544225.ListSpaces
end
