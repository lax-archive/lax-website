-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax253009.BooleanFourier
end

-- Lax253009.FourierProjection
section
namespace Lax253009.FourierProjection
end Lax253009.FourierProjection
end

-- Lax253009.SmallSupport
section
namespace Lax253009.SmallSupport

noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax253009.SmallSupport
end

-- Lax253009.FourierDecoding
section
namespace Lax253009.FourierDecoding

open BooleanFourier FourierProjection SmallSupport

axiom boolean_decoding_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Cube ι → Bool) (l : ℕ) (t : ℝ) :
  ((decodingSet (coefficient (fun x ↦ sign (A x))) l (Real.rpow 2 (-t))).card : ℝ) ≤
    Real.rpow 2 t

end Lax253009.FourierDecoding
end
