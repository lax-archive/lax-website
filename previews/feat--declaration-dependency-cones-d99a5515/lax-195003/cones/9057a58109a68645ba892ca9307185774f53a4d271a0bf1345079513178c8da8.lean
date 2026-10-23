-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax195003.WelzlOrders
section
namespace Lax195003.WelzlOrders

/-- A set system on `α`: a family of subsets of the ground set `α`. -/
abbrev SetSystem (α : Type*) := Set (Set α)

end Lax195003.WelzlOrders
end
