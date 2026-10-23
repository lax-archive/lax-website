-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Card

-- Lax683916.TwoUniformSetSystems
section
namespace Lax683916.TwoUniformSetSystems

/-- A family of two-element subsets of `V`. -/
structure TwoUniformSetSystem (V : Type*) where
  /-- The sets belonging to the family. -/
  sets : Set (Set V)
  /-- Every member of the family has exactly two elements. -/
  twoUniform : ∀ s ∈ sets, Set.ncard s = 2

end Lax683916.TwoUniformSetSystems
end
