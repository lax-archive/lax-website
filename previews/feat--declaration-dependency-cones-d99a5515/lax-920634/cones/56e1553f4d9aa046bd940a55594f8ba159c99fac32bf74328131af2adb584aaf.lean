-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find

-- Lax920634.SeedSearch
section
namespace Lax920634.SeedSearch

open Function

/-- The number of vertices of `S` whose image lies outside `S`. -/
def escape {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => f v ∉ S).card

end Lax920634.SeedSearch
end
