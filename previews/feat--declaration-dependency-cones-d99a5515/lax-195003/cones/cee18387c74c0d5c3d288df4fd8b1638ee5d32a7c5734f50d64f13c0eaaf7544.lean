-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax195003.WelzlOrders
section
namespace Lax195003.WelzlOrders

/-- The number of consecutive pairs in the order `π` with exactly one
endpoint in `X`. -/
noncomputable def crossingCount {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : ℕ :=
  {u : Fin n | ∃ v : Fin n,
    (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}.ncard

end Lax195003.WelzlOrders
end
