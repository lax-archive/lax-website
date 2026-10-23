-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- Lax570090.Geometry
section
namespace Lax570090.Geometry

/-- The real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- The finite point set contains three distinct collinear points. -/
def HasThreeCollinear (P : Finset Point) : Prop :=
  ∃ f : Fin 3 → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧ Collinear ℝ (Set.range f)

end Lax570090.Geometry
end
