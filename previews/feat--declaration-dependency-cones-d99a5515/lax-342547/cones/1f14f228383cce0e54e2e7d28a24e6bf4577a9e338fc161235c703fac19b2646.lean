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

def evaluation (S : J → Submodule Binary V) (C : Matrix J T Binary) :
    (∀ j, S j) →ₗ[Binary] (T → V) where
  toFun x t := ∑ j, C j t • (x j).val
  map_add' x y := by ext t; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext t; simp [Finset.smul_sum, smul_smul, mul_comm]

axiom evaluation_rank [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) (S₀ : Submodule Binary V)
    (hS : ∀ j, S₀ ≤ S j) (C : Matrix J T Binary) (hC : Function.Injective C.mulVec) :
    Fintype.card T * Module.finrank Binary S₀ ≤
      Module.finrank Binary (LinearMap.range (evaluation S C))

end Lax342547.AffineImages
end
