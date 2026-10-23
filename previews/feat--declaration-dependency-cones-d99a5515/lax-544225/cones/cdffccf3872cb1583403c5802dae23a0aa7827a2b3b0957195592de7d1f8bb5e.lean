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
namespace Lax544225.BinaryFloats.phi
end Lax544225.BinaryFloats.phi

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

/-- Canonical data for a nonzero finite number in a format. -/
structure FiniteValue (F : Format) where
  /-- Sign bit: 0 is positive and 1 is negative. -/
  sign : Fin 2
  /-- The exponent of the value. -/
  exponent : ℤ
  /-- The integer significand before scaling by 2^(−p). -/
  mantissa : ℕ
  /-- The exponent is allowed by the format. -/
  exponent_mem : F.minExponent ≤ exponent ∧ exponent ≤ F.maxExponent
  /-- The significand is nonzero and less than 2^(p+1). -/
  mantissa_mem : 0 < mantissa ∧ mantissa < 2 ^ (F.precision + 1)
  /-- A significand below the normal range occurs only at the minimum exponent. -/
  canonical : 2 ^ F.precision ≤ mantissa ∨ exponent = F.minExponent

/-- Canonical finite data and the four signed special values together with one NaN. -/
inductive Value (F : Format)
  /-- A nonzero finite floating-point value. -/
  | finite : FiniteValue F → Value F
  /-- A signed zero. -/
  | zero : Fin 2 → Value F
  /-- A signed infinity. -/
  | infinity : Fin 2 → Value F
  /-- The single, greatest NaN value. -/
  | nan : Value F

/-- The exact ordinary real value of canonical finite data. -/
noncomputable def finiteReal {F : Format} (f : FiniteValue F) : ℝ :=
  (-1 : ℝ) ^ f.sign.val * (2 : ℝ) ^ f.exponent *
    ((f.mantissa : ℝ) * (2 : ℝ) ^ (-(F.precision : ℤ)))

/-- The ordinary finite value used to order members within a finite category. -/
noncomputable def withinCategory {F : Format} : Value F → ℝ
  | .finite f => finiteReal f
  | _ => 0

end Lax544225.BinaryFloats
end
