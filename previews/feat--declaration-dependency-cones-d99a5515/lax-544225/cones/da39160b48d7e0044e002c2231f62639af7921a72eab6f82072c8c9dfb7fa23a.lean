-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Setoid.Partition
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

-- Lax544225.Classifier
section
namespace Lax544225
end Lax544225

namespace Lax544225.Classifier
end Lax544225.Classifier

namespace Lax544225.Classifier.Classifier
end Lax544225.Classifier.Classifier
end

-- Lax544225.Partitions
section
universe u

namespace Lax544225.Partitions

open Classifier

/-- A finite partition into nonempty parts with unique membership for every input. -/
def IsPartition {S : Type u} (P : Set (Set S)) : Prop :=
  P.Finite ∧ Setoid.IsPartition P

/-- The partition consisting of the whole carrier as its only part. -/
def IsTrivial {S : Type u} (P : Set (Set S)) : Prop := P = {Set.univ}

end Lax544225.Partitions
end

-- Lax544225.PartitionRobustness
section
universe u

namespace Lax544225.PartitionRobustness

open scoped NNReal

open Semimetric Partitions Balls

/-- Coverage by monochromatic balls whose centers are μ-close to the input. -/
def Robust {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (P : Set (Set S)) (_hP : IsPartition P) (μ ε : ℝ≥0) : Prop :=
  ∀ x, ∃ x', x' ∈ ball d hd x μ ∧ ∃ A ∈ P, x ∈ A ∧ ball d hd x' ε ⊆ A

/-- Every robust finite partition of the carrier has only the whole carrier as a part. -/
def OnlyTrivial {S : Type u} (d : Distance S) (hd : IsSemimetric d) (μ ε : ℝ≥0) : Prop :=
  ∀ P (hP : IsPartition P), Robust d hd P hP μ ε → IsTrivial P

end Lax544225.PartitionRobustness
end

-- Lax544225.BoundaryExistence
section
universe u

namespace Lax544225.BoundaryExistence

open scoped NNReal

open Semimetric OrderedSemimetric PartitionRobustness Boundary Balls

/-- In a finite totally ordered semimetric space, only-trivial robustness is equivalent to opposite-boundary covering of every nonempty proper cut. -/
axiom statement {S : Type u} [Finite S] [LinearOrder S] (d : Distance S)
    (hd : IsOrdered d (· ≤ ·)) (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd.1 μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd.1 x μ ∩ A ⊆ neighborhood d hd.1 (complementBoundary A) ε) ∨
        (x ∈ Aᶜ ∧ ball d hd.1 x μ ∩ Aᶜ ⊆ neighborhood d hd.1 (boundary A) ε))

end Lax544225.BoundaryExistence
end
