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

/-- The number of consecutive pairs in the order `π` with exactly one
endpoint in `X`. -/
noncomputable def crossingCount {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : ℕ :=
  {u : Fin n | ∃ v : Fin n,
    (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}.ncard

/-- The crossing number of `π` with respect to `𝓕`: the largest crossing
count of a member of the set system. -/
noncomputable def crossingNumber {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) : ℕ :=
  sSup {k : ℕ | ∃ X ∈ 𝓕, k = crossingCount π X}

/-- The order `π` is a Welzl order of crossing number at most `k` for the
set system `𝓕`. -/
def IsWelzlOrder {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  crossingNumber 𝓕 π ≤ k

end Lax195003.WelzlOrders
end
