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

/-- `p` and `q` see one another with respect to the ambient finite set `P`. -/
def Visible (P : Finset Point) (p q : Point) : Prop :=
  p ≠ q ∧ ∀ r ∈ P, r ∉ openSegment ℝ p q

/-- The point-visibility graph of `P`; its vertices retain their membership proofs. -/
def visibilityGraph (P : Finset Point) : SimpleGraph P where
  Adj p q := Visible P p q
  symm := ⟨fun p q hpq ↦
    ⟨hpq.1.symm, fun r hr ↦ (openSegment_symm ℝ q.val p.val) ▸ hpq.2 r hr⟩⟩
  loopless := ⟨fun p hp => hp.1 rfl⟩

end Lax570090.Geometry
end
