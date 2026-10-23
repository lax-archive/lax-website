-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Lattice

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

end Lax544225.Balls
end

-- Lax544225.Classifier
section
universe u

namespace Lax544225.Classifier

/-- A total classifier in which every label occurs. -/
structure Classifier (S : Type u) (n : ℕ) where
  /-- The label assigned to each input. -/
  label : S → Fin n
  /-- Every class has a representative. -/
  surjective : Function.Surjective label

end Lax544225.Classifier
end

-- Lax544225.ClassifierRobustness
section
universe u

namespace Lax544225.ClassifierRobustness

open scoped NNReal

open Classifier Semimetric Balls

/-- Local robustness of the classifier at x. -/
def LocallyRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetric d)
    (c : Classifier S n) (ε : ℝ≥0) (x : S) : Prop :=
  ∀ y ∈ ball d hd x ε, c.label y = c.label x

/-- Local robustness at every input. -/
def GloballyRobust {S : Type u} {n : ℕ} (d : Distance S) (hd : IsSemimetric d)
    (c : Classifier S n) (ε : ℝ≥0) : Prop :=
  ∀ x, LocallyRobust d hd c ε x

end Lax544225.ClassifierRobustness
end
