-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Setoid.Partition

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

-- Lax544225.GeneralExistence
section
universe u

namespace Lax544225.GeneralExistence

open scoped NNReal

open Semimetric PartitionRobustness Balls

/-- The trivial partition is the only robust partition exactly when every nonempty proper cut admits a covering point on one side from ε-balls centered on the other side. -/
axiom statement {S : Type u} (d : Distance S) (hd : IsSemimetric d)
    (μ ε : ℝ≥0) (hε : 0 < ε) :
    OnlyTrivial d hd μ ε ↔ (∀ A : Set S, A.Nonempty → Aᶜ.Nonempty →
      ∃ x, (x ∈ A ∧ ball d hd x μ ⊆ neighborhood d hd Aᶜ ε) ∨
        (x ∈ Aᶜ ∧ ball d hd x μ ⊆ neighborhood d hd A ε))

end Lax544225.GeneralExistence
end
