-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.NNReal.Basic
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

/-- Exact additivity of distance along the given ordered chains. -/
def Additive {S : Type u} (d : Distance S) (le : S → S → Prop) : Prop :=
  ∀ a b c, le a b → le b c → d a c = d a b + d b c

end Lax544225.OrderedSemimetric
end

-- Lax544225.SumProductSpace
section
universe u

namespace Lax544225.SumProductSpace

open Semimetric OrderedSemimetric

open scoped BigOperators

/-- Coordinatewise order on finite tuples. -/
def productLe {S : Type u} (le : S → S → Prop) (n : ℕ) (f g : Fin n → S) : Prop :=
  ∀ i, le (f i) (g i)

end Lax544225.SumProductSpace
end

-- Lax544225.MaximumProductSpace
section
universe u

namespace Lax544225.MaximumProductSpace

open Semimetric OrderedSemimetric SumProductSpace

/-- Coordinatewise order restricted to equal distances in every coordinate. -/
def synchronizedLe {S : Type u} (d : Distance S) (le : S → S → Prop) (n : ℕ)
    (f g : Fin n → S) : Prop :=
  productLe le n f g ∧ ∀ i j, d (f i) (g i) = d (f j) (g j)

/-- Maximum of the base distances between corresponding coordinates. -/
noncomputable def maxDistance {S : Type u} (d : Distance S) (n : ℕ) : Distance (Fin n → S) :=
  fun f g => Finset.univ.sup (fun i => d (f i) (g i))

/-- Synchronized maximum products preserve ordered semimetric spaces. -/
axiom statement {S : Type u} (d : Distance S) (le : S → S → Prop)
    (hd : IsOrdered d le) (hadd : Additive d le) (n : ℕ) :
    IsOrdered (maxDistance d n) (synchronizedLe d le n)

end Lax544225.MaximumProductSpace
end
