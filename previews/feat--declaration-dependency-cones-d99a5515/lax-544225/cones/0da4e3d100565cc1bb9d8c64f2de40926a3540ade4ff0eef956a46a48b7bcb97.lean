-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
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

-- Lax544225.BinaryFloats
section
namespace Lax544225.BinaryFloats.FiniteValue
end Lax544225.BinaryFloats.FiniteValue

namespace Lax544225.BinaryFloats.Value
end Lax544225.BinaryFloats.Value

namespace Lax544225.BinaryFloats.phi
end Lax544225.BinaryFloats.phi

namespace Lax544225.BinaryFloats.withinCategory
end Lax544225.BinaryFloats.withinCategory

namespace Lax544225.BinaryFloats.Value.finite
end Lax544225.BinaryFloats.Value.finite

namespace Lax544225.BinaryFloats.Value.infinity
end Lax544225.BinaryFloats.Value.infinity

namespace Lax544225.BinaryFloats.Value.nan
end Lax544225.BinaryFloats.Value.nan

namespace Lax544225.BinaryFloats.Value.zero
end Lax544225.BinaryFloats.Value.zero

universe u

namespace Lax544225.BinaryFloats

open scoped NNReal

/-- The precision and nonempty exponent interval of a binary format. -/
structure Format where
  /-- Number of fractional bits in the significand. -/
  precision : ℕ
  /-- Least allowed exponent. -/
  minExponent : ℤ
  /-- Greatest allowed exponent. -/
  maxExponent : ℤ
  /-- The exponent interval is nonempty. -/
  exponent_le : minExponent ≤ maxExponent

end Lax544225.BinaryFloats
end
