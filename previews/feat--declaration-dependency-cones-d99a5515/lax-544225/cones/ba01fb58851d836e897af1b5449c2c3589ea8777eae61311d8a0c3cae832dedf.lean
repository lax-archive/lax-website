-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Setoid.Partition

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

-- Lax544225.Partitions
section
universe u

namespace Lax544225.Partitions

open Classifier

/-- The part assigned a particular classifier label. -/
def fiber {S : Type u} {n : ℕ} (c : Classifier S n) (i : Fin n) : Set S :=
  {x | c.label x = i}

/-- The collection of all label fibers. -/
def induced {S : Type u} {n : ℕ} (c : Classifier S n) : Set (Set S) :=
  Set.range (fiber c)

end Lax544225.Partitions
end
