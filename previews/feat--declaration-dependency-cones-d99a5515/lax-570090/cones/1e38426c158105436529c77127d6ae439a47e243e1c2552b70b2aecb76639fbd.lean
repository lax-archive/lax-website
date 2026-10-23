-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Independent
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

-- Lax570090.ConvexLayers
section
namespace Lax570090.ConvexLayers

open Lax570090.Geometry

open scoped Classical

/-- Every point is a vertex: no point lies in the convex hull of the others. -/
def ConvexPosition (P : Finset Point) : Prop :=
  ConvexIndependent ℝ (fun p : {p : Point // p ∈ P} ↦ p.val)

/-- Vertices of the convex hull, including all points of sets of size at most two. -/
noncomputable def extremeLayer (P : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ)

/-- The remainder after deleting the current outer layer. -/
noncomputable def inner (P : Finset Point) : Finset Point := P \ extremeLayer P

/-- The remainder after `n` layers have been removed. -/
noncomputable def remainder (P : Finset Point) : ℕ → Finset Point
  | 0 => P
  | n + 1 => inner (remainder P n)

/-- Layers are indexed from zero: `layer P 0` is the outer layer. -/
noncomputable def layer (P : Finset Point) (n : ℕ) : Finset Point :=
  extremeLayer (remainder P n)

/-- The exact minimality condition in the proposed four-layer lemma. -/
def MinimalOuter (S : Finset Point) : Prop :=
  ∀ X ⊆ S, ConvexPosition X → (extremeLayer S).card ≤ X.card → X = extremeLayer S

/-- An unordered empty convex polygon with exactly `k` vertices. -/
def EmptyPolygon (P H : Finset Point) (k : ℕ) : Prop :=
  H ⊆ P ∧ H.card = k ∧ ConvexPosition H ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (H : Set Point) → p ∈ H

def HasEmptyHexagon (P : Finset Point) : Prop :=
  ∃ H, EmptyPolygon P H 6

end Lax570090.ConvexLayers
end

-- Lax570090.ValtrFourLayer
section
namespace Lax570090.ValtrFourLayer

open Lax570090.Geometry Lax570090.ConvexLayers

/-- The weakened four-layer lemma requested for the unoptimized proof.
`layer S 3` is the fourth layer because layer indices start at zero. -/
axiom exists_emptyHexagon_of_four_layers
    (S : Finset Point) (hgeneral : ¬HasThreeCollinear S)
    (hminimal : MinimalOuter S) (hlarge : 16 ≤ (extremeLayer S).card)
    (hfourth : (layer S 3).Nonempty) : HasEmptyHexagon S

end Lax570090.ValtrFourLayer
end
