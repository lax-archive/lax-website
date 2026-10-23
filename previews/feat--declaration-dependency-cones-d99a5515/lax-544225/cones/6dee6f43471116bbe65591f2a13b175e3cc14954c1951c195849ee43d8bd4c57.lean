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

-- Lax544225.PrecisionGaps
section
universe u

namespace Lax544225.PrecisionGaps

open scoped NNReal

open Semimetric OrderedSemimetric

/-- The number of consecutive steps between the endpoints of a closed interval. -/
noncomputable def steps {S : Type u} [PartialOrder S] (x y : S) : ℕ :=
  (Set.Icc x y).ncard - 1

/-- The largest average distance per ordered step. -/
noncomputable def deltaUpper {S : Type u} [Finite S] [PartialOrder S] (d : Distance S)
    (_hd : IsOrdered d (· ≤ ·)) : ℝ≥0 :=
  sSup {r | ∃ x y, x < y ∧ r = d x y / (steps x y : ℝ≥0)}

end Lax544225.PrecisionGaps
end
