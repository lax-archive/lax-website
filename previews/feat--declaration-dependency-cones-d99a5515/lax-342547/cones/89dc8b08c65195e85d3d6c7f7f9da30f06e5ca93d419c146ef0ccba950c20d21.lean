-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.QuadraticForm.Prod
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

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic
end Lax342547.FormalQuadratic
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

end Lax342547.Walsh
end

-- Lax342547.QuadraticBias
section
namespace Lax342547.QuadraticBias

open Lax342547.MomentSpace Lax342547.Walsh

open scoped BigOperators

axiom quadratic_bias_rank_bound {V : Type} [AddCommGroup V] [Module Binary V]
    [Fintype V] [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V) (r : ℕ)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (hrank : 2*r ≤ Module.finrank Binary (LinearMap.range B)) :
    |(∑ x, sign (Q x))/(Fintype.card V : ℝ)| ≤ 1/(2 : ℝ)^r

end Lax342547.QuadraticBias
end
