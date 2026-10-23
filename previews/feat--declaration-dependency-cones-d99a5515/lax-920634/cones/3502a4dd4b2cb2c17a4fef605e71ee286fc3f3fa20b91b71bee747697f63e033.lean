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

/-- A table of thirty maps on a numbered finite vertex set. -/
abbrev Table (n : ℕ) := Fin 30 → Fin n → Fin n

/-- The candidate table represented by a base-`n` integer. -/
def decode (n : ℕ) (code : Fin (n ^ (30 * n))) : Table n :=
  fun i v => finFunctionFinEquiv.symm code (finProdFinEquiv (i, v))

end Lax920634.SeedSearch
end
