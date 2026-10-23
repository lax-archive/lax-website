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
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns

open Lax342547.MomentSpace

open scoped ENNReal

variable {I J N : Type} [Fintype I] [Fintype J] [Fintype N]

abbrev GramFiber (A : Matrix N I Binary) (G : Matrix I J Binary) :=
  {B : Matrix N J Binary // A.transpose * B = G}

noncomputable instance (A : Matrix N I Binary) (G : Matrix I J Binary) : Fintype (GramFiber A G) := by
  classical exact Subtype.fintype _

axiom conditional_failure [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) (G : Matrix I J Binary)
    [Nonempty (GramFiber A G)] :
    (PMF.uniformOfFintype (GramFiber A G)).toOuterMeasure {B | ¬ Function.Injective B.val.mulVec} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N

end Lax342547.GramColumns
end
