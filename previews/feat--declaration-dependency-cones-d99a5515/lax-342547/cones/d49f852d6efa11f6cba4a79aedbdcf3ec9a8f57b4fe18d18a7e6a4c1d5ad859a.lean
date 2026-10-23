-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages

open Lax342547.MomentSpace

open scoped ENNReal

variable {J T V : Type} [Fintype J] [Fintype T]
  [AddCommGroup V] [Module Binary V]

def columnMap (v : J → V) : (J → Binary) →ₗ[Binary] V where
  toFun c := ∑ j, c j • v j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' s c := by simp [Finset.smul_sum, smul_smul]

axiom dependence_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | ¬ Function.Injective (columnMap (fun j => a j + (x j).val))} ≤
      (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Module.finrank Binary S₀

end Lax342547.AffineImages
end
