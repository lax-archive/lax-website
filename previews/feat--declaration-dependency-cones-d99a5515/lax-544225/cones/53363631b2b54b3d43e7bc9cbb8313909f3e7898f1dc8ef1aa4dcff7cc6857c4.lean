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

/-- Equal-length coordinatewise order with equal base distances across coordinates. -/
def synchronizedListLe {S : Type u} (d : Distance S) (le : S → S → Prop)
    (pad : S) (f g : List S) : Prop :=
  listLe le pad f g ∧ ∀ i < f.length, ∀ j < f.length,
    d (f.getD i pad) (g.getD i pad) = d (f.getD j pad) (g.getD j pad)

/-- A positive penalty that distinguishes different list lengths. -/
def lengthPenalty {S : Type u} (f g : List S) : ℝ≥0 :=
  if f.length = g.length then 0 else 1

/-- Sum of padded coordinate distances, plus the length penalty. -/
noncomputable def sumDistance {S : Type u} (d : Distance S) (pad : S) : Distance (List S) :=
  fun f g => lengthPenalty f g +
    ∑ i ∈ Finset.range (max f.length g.length), d (f.getD i pad) (g.getD i pad)

/-- Maximum padded coordinate distance, plus the length penalty. -/
noncomputable def maxDistance {S : Type u} (d : Distance S) (pad : S) : Distance (List S) :=
  fun f g => lengthPenalty f g +
    (Finset.range (max f.length g.length)).sup (fun i => d (f.getD i pad) (g.getD i pad))

/-- Both padded-list constructions are ordered semimetric spaces. -/
axiom statement :
    (∀ {S : Type u} (d : Distance S) (le : S → S → Prop),
      IsOrdered d le → ∀ pad : S,
        IsOrdered (Lax544225.ListSpaces.sumDistance d pad) (Lax544225.ListSpaces.listLe le pad)) ∧
    (∀ {S : Type u} (d : Distance S) (le : S → S → Prop),
      IsOrdered d le → Additive d le → ∀ pad : S,
        IsOrdered (Lax544225.ListSpaces.maxDistance d pad)
          (Lax544225.ListSpaces.synchronizedListLe d le pad))

end Lax544225.ListSpaces
end
