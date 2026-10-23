-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Cover

-- Lax544225.Semimetric
section
namespace Lax544225
end Lax544225

namespace Lax544225.Semimetric
end Lax544225.Semimetric
end

-- Lax544225.Balls
section
namespace Lax544225.Balls
end Lax544225.Balls
end

-- Lax544225.Boundary
section
universe u

namespace Lax544225.Boundary

open scoped NNReal

open Semimetric Balls

/-- Consecutive points in a linear order. -/
abbrev Successor {S : Type u} [LinearOrder S] (x y : S) : Prop :=
  CovBy x y

end Lax544225.Boundary
end
