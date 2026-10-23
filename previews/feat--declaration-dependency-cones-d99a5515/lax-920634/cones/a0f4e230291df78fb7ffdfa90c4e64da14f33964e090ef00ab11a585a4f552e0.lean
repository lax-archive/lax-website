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

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

/-- The fixed number of seed vertices, the fourth power of its degree. -/
def seedOrder : ℕ := seedDegree ^ 4

end Lax920634.SeedSearch
end
