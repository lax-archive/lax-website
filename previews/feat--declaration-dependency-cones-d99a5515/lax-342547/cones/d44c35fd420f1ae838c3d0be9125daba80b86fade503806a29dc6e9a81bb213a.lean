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

axiom subprobability_dot_bound {I : Type} [Fintype I] [DecidableEq I]
    (α β f g : (I → Binary) → ℝ) (p₁ p₂ : ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ p₁) (hβ : ∀ y, 0 ≤ β y ∧ β y ≤ p₂)
    (hαsum : ∑ x, α x ≤ 1) (hβsum : ∑ y, β y ≤ 1)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |∑ x, ∑ y, α x * β y * f x * g y * phase x y| ≤
      Real.sqrt ((2 : ℝ) ^ Fintype.card I * p₁ * p₂)

end Lax342547.Walsh
end
