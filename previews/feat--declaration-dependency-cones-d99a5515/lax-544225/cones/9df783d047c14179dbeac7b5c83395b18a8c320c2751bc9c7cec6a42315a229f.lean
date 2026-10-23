-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs.PartialOrder

-- Lax544225.Semimetric
section
universe u

namespace Lax544225.Semimetric

open scoped NNReal

/-- A nonnegative real-valued distance on a carrier. -/
abbrev Distance (S : Type u) := S → S → ℝ≥0

/-- The defining properties of a semimetric space, including a nonempty carrier. -/
def IsSemimetric {S : Type u} (d : Distance S) : Prop :=
  Nonempty S ∧ (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x)

end Lax544225.Semimetric
end

-- Lax544225.OrderedSemimetric
section
universe u

namespace Lax544225.OrderedSemimetric

open Semimetric

/-- The semimetric, partial-order, and ordered-chain distance laws. -/
def IsOrdered {S : Type u} (d : Distance S) (le : S → S → Prop) : Prop :=
  IsSemimetric d ∧ IsPartialOrder S le ∧
    (∀ a b c, le a b → le b c → d a b + d b c ≤ d a c)

end Lax544225.OrderedSemimetric
end

-- Lax544225.BinaryFloats
section
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

/-- The real embedding including separated signed zeros and bounded special values. -/
noncomputable def phi (F : Format) : Value F → ℝ
  | .finite f => finiteReal f
  | .zero s => if s.val = 0 then 0 else -(2 : ℝ) ^ (F.minExponent - (F.precision : ℤ) - 1)
  | .infinity s => if s.val = 0 then (2 : ℝ) ^ (F.maxExponent + 1)
    else -(2 : ℝ) ^ (F.maxExponent + 1)
  | .nan => (2 : ℝ) ^ (F.maxExponent + 1) + 1

/-- The position of each sign and special-value category in the total order. -/
def category {F : Format} : Value F → ℕ
  | .finite f => if f.sign.val = 0 then 4 else 1
  | .zero s => if s.val = 0 then 3 else 2
  | .infinity s => if s.val = 0 then 5 else 0
  | .nan => 6

/-- The ordinary finite value used to order members within a finite category. -/
noncomputable def withinCategory {F : Format} : Value F → ℝ
  | .finite f => finiteReal f
  | _ => 0

/-- IEEE category order with one positive NaN and exact comparison of finite values. -/
def ieeeLe (F : Format) (x y : Value F) : Prop :=
  category x < category y ∨
    (category x = category y ∧ withinCategory x ≤ withinCategory y)

end Lax544225.BinaryFloats
end

-- Lax544225.FloatAbsoluteSpace
section
universe u

namespace Lax544225.FloatAbsoluteSpace

open BinaryFloats OrderedSemimetric

open scoped NNReal

/-- Absolute embedded distance d₁. -/
noncomputable def absDistance (F : Format) (x y : Value F) : ℝ≥0 :=
  Real.toNNReal (|phi F x - phi F y|)

/-- The absolute-distance construction is an ordered semimetric space. -/
axiom statement (F : Format) : IsOrdered (absDistance F) (ieeeLe F)

end Lax544225.FloatAbsoluteSpace
end
