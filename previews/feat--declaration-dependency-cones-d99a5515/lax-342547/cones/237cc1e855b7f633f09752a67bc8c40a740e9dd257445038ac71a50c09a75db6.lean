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
end Lax342547.GramColumns
end

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization

open Lax342547.MomentSpace

open scoped ENNReal

noncomputable def probability {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Matrix N I Binary × Matrix N J Binary)).toOuterMeasure
    {z | Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

end Lax342547.GramNormalization
end

-- Lax342547.HistogramGram
section
namespace Lax342547.HistogramGram

open Lax342547.MomentSpace

open scoped BigOperators

noncomputable def normalized {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) : ℝ :=
  (2 : ℝ)^(Fintype.card I*Fintype.card J)*(Lax342547.GramNormalization.probability (N := N) G).toReal

axiom normalized_bounds {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N) :
    0 ≤ normalized (N := N) G ∧ normalized (N := N) G ≤ 1 ∧
      1-2*((2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N) ≤ normalized (N := N) G

end Lax342547.HistogramGram
end
