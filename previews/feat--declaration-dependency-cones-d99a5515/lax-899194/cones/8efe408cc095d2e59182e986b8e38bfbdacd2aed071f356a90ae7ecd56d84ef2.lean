-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

-- Lax899194.NetworkCreationGame
section
namespace Lax899194.NetworkCreationGame

/-- The other players to which player `i` purchases edges. -/
def Strategy (n : ℕ) (i : Fin n) := { S : Set (Fin n) // i ∉ S }

/-- A choice of strategy for every player. -/
abbrev Profile (n : ℕ) := (i : Fin n) → Strategy n i

end Lax899194.NetworkCreationGame
end
