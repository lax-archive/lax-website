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
end Lax342547.GramNormalization
end

-- Lax342547.ReferenceKeys
section
namespace Lax342547.ReferenceKeys

open Lax342547.MomentSpace

open scoped ENNReal

abbrev Tuples (Comp : Type) (Pos : Comp → Type) (N : Type) :=
  ∀ e, Matrix N (Pos e) Binary × Matrix N (Pos e) Binary

noncomputable def space {Comp : Type} (Pos : Comp → Type) (N : Type)
    [∀ e, Fintype (Pos e)] [Fintype N] (G : ∀ e, Matrix (Pos e) (Pos e) Binary) :
    Set (Tuples Comp Pos N) := {x | ∀ e, (x e).1.transpose * (x e).2 = G e}

axiom reference_density_lower {Comp N : Type} [Fintype Comp] [Fintype N]
    [DecidableEq Comp] [DecidableEq N]
    (Pos : Comp → Type) [∀ e, Fintype (Pos e)] [∀ e, DecidableEq (Pos e)]
    (G : ∀ e, Matrix (Pos e) (Pos e) Binary)
    (hN : ∀ e, 2 * Fintype.card (Pos e) + 1 ≤ Fintype.card N) :
    (∏ e, 1 / (2 : ℝ≥0∞) ^ (Fintype.card (Pos e) * Fintype.card (Pos e) + 2)) ≤
      (PMF.uniformOfFintype (Tuples Comp Pos N)).toOuterMeasure (space Pos N G)

end Lax342547.ReferenceKeys
end
