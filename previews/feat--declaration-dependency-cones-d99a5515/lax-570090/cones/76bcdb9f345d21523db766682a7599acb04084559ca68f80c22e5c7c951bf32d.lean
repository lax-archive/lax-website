-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- Lax570090.Geometry
section
namespace Lax570090.Geometry

/-- The real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- The signed twice-area of the oriented triangle `p q r`. -/
def turn (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The finite point set contains three distinct collinear points. -/
def HasThreeCollinear (P : Finset Point) : Prop :=
  ∃ f : Fin 3 → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧ Collinear ℝ (Set.range f)

end Lax570090.Geometry
end

-- Lax570090.HujterKisfaludiBak
section
namespace Lax570090.HujterKisfaludiBak

open Lax570090.Geometry

/-- Six labelled vertices in strict counterclockwise cyclic convex position.

The last conjunct records the complete cyclic order type, not merely its six
supporting-edge consequences.  This is useful in the direct geometric proof:
an increasing triple of cyclic labels is positively oriented. -/
def StrictConvexHexagon (h : Fin 6 → Point) : Prop :=
  Function.Injective h ∧
    (∀ i j : Fin 6, j ≠ i → j ≠ i + 1 →
      0 < turn (h i) (h (i + 1)) (h j)) ∧
    ∀ i j k : Fin 6, i < j → j < k →
      0 < turn (h i) (h j) (h k)

/-- A convex hexagon whose convex hull contains no further point of `P`. -/
def EmptyConvexHexagon (P : Finset Point) (h : Fin 6 → Point) : Prop :=
  StrictConvexHexagon h ∧
    (∀ i, h i ∈ P) ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (Set.range h) → p ∈ Set.range h

/-- The deliberately unoptimized Valtr bound `h(6) ≤ 2^428 + 1`, via 216
points in convex position. Its proof in `Lax570090Proofs.EmptyHexagon` uses the
four-layer theorem interface, whose proof is also in this package. The
visibility-colouring argument uses this interface so Lax records the dependency;
the composed proof tree uses only standard logical axioms. -/
axiom exists_emptyConvexHexagon
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card)
    (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h

end Lax570090.HujterKisfaludiBak
end
