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
import Mathlib.LinearAlgebra.Matrix.ToLin
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

-- Lax342547.MixerCompatibility
section
namespace Lax342547.MixerCompatibility

variable {K I E F : Type} [Field K] [Fintype I] [Fintype E] [Fintype F]

def restrictions (Z : Matrix I E K) (W : Matrix I F K) :
    Matrix I I K →ₗ[K] Matrix E I K × Matrix I F K where
  toFun L := (Z.transpose * L, L * W)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c L := by simp [Matrix.mul_smul, Matrix.smul_mul]

end Lax342547.MixerCompatibility
end

-- Lax342547.MixerRowLaw
section
namespace Lax342547.MixerRowLaw

variable {K I E F N : Type} [Field K] [Fintype I]

def directions (D : Matrix I N K) :
    (Matrix E I K × Matrix I F K) →ₗ[K] (Matrix E N K × Matrix N F K) where
  toFun p := (p.1 * D, D.transpose * p.2)
  map_add' x y := by simp [Matrix.add_mul, Matrix.mul_add]
  map_smul' c x := by simp [Matrix.smul_mul, Matrix.mul_smul]

def observations (Z : Matrix I E K) (W : Matrix I F K) (D : Matrix I N K) :
    Matrix I I K →ₗ[K] (Matrix E N K × Matrix N F K) :=
  (directions D).comp (MixerCompatibility.restrictions Z W)

open Lax342547.MomentSpace

open scoped ENNReal

axiom row_law_bound {I E F N : Type} [Fintype I] [Fintype E] [Fintype F] [Fintype N]
    [DecidableEq I] [DecidableEq E] [DecidableEq F] [DecidableEq N]
    (Z : Matrix I E Binary) (W : Matrix I F Binary) (D : Matrix I N Binary)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) (hD : Function.Injective D.mulVec)
    (y : Matrix E N Binary × Matrix N F Binary) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (observations Z W D) y ≤
      2 ^ (Fintype.card E * Fintype.card F) * PMF.uniformOfFintype (Matrix E N Binary × Matrix N F Binary) y

end Lax342547.MixerRowLaw
end
