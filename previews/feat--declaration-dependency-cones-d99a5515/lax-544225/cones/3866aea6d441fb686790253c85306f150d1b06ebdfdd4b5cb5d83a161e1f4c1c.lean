-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Cover
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

-- Lax544225.Balls
section
universe u

namespace Lax544225.Balls

open scoped NNReal

open Semimetric

/-- The closed ball centered at x with radius r. -/
def ball {S : Type u} (d : Distance S) (_hd : IsSemimetric d)
    (x : S) (r : ℝ≥0) : Set S :=
  {y | d y x ≤ r}

/-- The union of closed r-balls with centers in A. -/
def neighborhood {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (A : Set S) (r : ℝ≥0) : Set S :=
  {y | ∃ x ∈ A, y ∈ ball d hd x r}

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

/-- Points of A adjacent to its complement in the ambient order. -/
def boundary {S : Type u} [LinearOrder S] (A : Set S) : Set S :=
  {x | x ∈ A ∧ ∃ y ∈ Aᶜ, Successor x y ∨ Successor y x}

/-- Points outside A adjacent to A in the ambient order. -/
def complementBoundary {S : Type u} [LinearOrder S] (A : Set S) : Set S :=
  boundary Aᶜ

end Lax544225.Boundary
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

-- Lax544225.BoundaryCoveringCharacterization
section
universe u

namespace Lax544225.BoundaryCoveringCharacterization

open scoped NNReal

open Semimetric OrderedSemimetric Balls Boundary

/-- In a finite totally ordered semimetric space, covering every proper cut is equivalent to covering its within-side μ-ball from the opposite boundary. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ⊆ neighborhood d hd.1 A ε)) ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε))

end Lax544225.BoundaryCoveringCharacterization
end
