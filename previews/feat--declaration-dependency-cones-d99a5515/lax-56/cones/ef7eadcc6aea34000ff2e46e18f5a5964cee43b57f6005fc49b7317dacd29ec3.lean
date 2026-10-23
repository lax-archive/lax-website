-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- Lax56.Geometry
section
namespace Lax56.Geometry

/-- The real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- `p` and `q` see one another with respect to the ambient finite set `P`. -/
def Visible (P : Finset Point) (p q : Point) : Prop :=
  p ≠ q ∧ ∀ r ∈ P, r ∉ openSegment ℝ p q

/-- The finite point set contains four distinct collinear points. -/
def HasFourCollinear (P : Finset Point) : Prop :=
  ∃ f : Fin 4 → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧ Collinear ℝ (Set.range f)

/-- The finite point set contains `k` points that pairwise see one another. -/
def HasVisibleClique (P : Finset Point) (k : ℕ) : Prop :=
  ∃ f : Fin k → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧
      Set.Pairwise (Set.range f) (Visible P)

end Lax56.Geometry
end

-- Lax56.MainTheorem
section
namespace Lax56.MainTheorem

open Lax56.Geometry

axiom large_point_set_four_collinear_or_visible_six
    (P : Finset Point) (hP : 10 ^ (2 ^ 450) ≤ P.card) :
    HasFourCollinear P ∨ HasVisibleClique P 6

end Lax56.MainTheorem
end
