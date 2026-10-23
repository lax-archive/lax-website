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

open Lax342547.MomentSpace

open scoped ENNReal

axiom uniform_image_bound {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] [Fintype V] [Fintype W]
    [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (f : V →ₗ[Binary] W) (c : ℕ)
    (hc : Module.finrank Binary W ≤ Module.finrank Binary (LinearMap.range f) + c) (y : W) :
    (PMF.uniformOfFintype V).map f y ≤ 2 ^ c * PMF.uniformOfFintype W y

end Lax342547.FiniteLinearLaw
end
