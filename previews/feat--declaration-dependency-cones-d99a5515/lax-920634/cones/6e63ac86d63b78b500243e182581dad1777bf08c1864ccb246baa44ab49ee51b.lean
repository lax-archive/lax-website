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

/-- Find the inverse image by scanning a numbered finite vertex set. -/
def inverse {n : ℕ} (f : Fin n → Fin n) (v : Fin n) : Fin n :=
  ((List.finRange n).find? fun u => decide (f u = v)).getD v

end Lax920634.SeedSearch
end
