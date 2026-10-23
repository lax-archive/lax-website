-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

end Lax342547.Walsh
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def correlation {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  ∑ x, ∑ y, f x * g y * phase x (A.mulVec y)

noncomputable def average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  correlation A f g / (2 ^ Fintype.card I * 2 ^ Fintype.card J)

axiom conditional_mixture_bound {T : Type} [Fintype T] {I J : T → Type}
    [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (I t)] [∀ t, DecidableEq (J t)]
    (A : ∀ t, Matrix (I t) (J t) Binary)
    (f : ∀ t, (I t → Binary) → ℝ) (g : ∀ t, (J t → Binary) → ℝ)
    (w C₁ C₂ : T → ℝ) (R : ℕ) (hw : ∀ t, 0 ≤ w t)
    (hC₁ : ∀ t, 0 ≤ C₁ t) (hC₂ : ∀ t, 0 ≤ C₂ t)
    (hf : ∀ t x, |f t x| ≤ C₁ t) (hg : ∀ t y, |g t y| ≤ C₂ t)
    (hR : ∀ t, R ≤ (A t).rank) :
    |∑ t, w t * average (A t) (f t) (g t)| ≤
      (∑ t, w t * C₁ t * C₂ t) / Real.sqrt ((2 : ℝ) ^ R)

end Lax342547.BilinearWalsh
end
