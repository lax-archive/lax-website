-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.FreshBitSampling
section
namespace Lax323828.FreshBitSampling

open FiniteProbability

def modulo {N r B : ℕ} (hr : 0 < r) (z : Fin N → Fin B) : Fin N → Fin r :=
  fun i ↦ ⟨(z i).val % r, Nat.mod_lt _ hr⟩

def bitsPerDraw (N r : ℕ) : ℕ := Nat.clog 2 (12 * N * r)

def binaryEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2 ^ b) :=
  (Equiv.piCongrRight (fun _ ↦ finTwoEquiv.symm)).trans finFunctionFinEquiv

def sample {N r : ℕ} (hr : 0 < r)
    (z : Fin N → Fin (bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  modulo hr (fun i ↦ binaryEquiv (bitsPerDraw N r) (z i))

def coinEquiv (N b : ℕ) : (Fin (N * b) → Bool) ≃ (Fin N → Fin b → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def sampleFlat {N r : ℕ} (hr : 0 < r)
    (coins : Fin (N * bitsPerDraw N r) → Bool) : Fin N → Fin r :=
  sample hr (coinEquiv N (bitsPerDraw N r) coins)

axiom flat_one_third_error {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (P : (Fin N → Fin r) → Prop) (hP : probability P ≤ 1 / 4) :
  probability (fun coins : Fin (N * bitsPerDraw N r) → Bool ↦ P (sampleFlat hr coins)) ≤ 1 / 3

end Lax323828.FreshBitSampling
end
