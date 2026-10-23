-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic

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
