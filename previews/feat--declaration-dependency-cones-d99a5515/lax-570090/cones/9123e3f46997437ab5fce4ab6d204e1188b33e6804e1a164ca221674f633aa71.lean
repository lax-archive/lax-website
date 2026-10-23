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

end Lax570090.Geometry
end

-- Lax570090.ConvexLayers
section
namespace Lax570090.ConvexLayers.remainder
end Lax570090.ConvexLayers.remainder

namespace Lax570090.ConvexLayers

open Lax570090.Geometry

open scoped Classical

/-- Every point is a vertex: no point lies in the convex hull of the others. -/
def ConvexPosition (P : Finset Point) : Prop :=
  ConvexIndependent ℝ (fun p : {p : Point // p ∈ P} ↦ p.val)

/-- Vertices of the convex hull, including all points of sets of size at most two. -/
noncomputable def extremeLayer (P : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ)

/-- The exact minimality condition in the proposed four-layer lemma. -/
def MinimalOuter (S : Finset Point) : Prop :=
  ∀ X ⊆ S, ConvexPosition X → (extremeLayer S).card ≤ X.card → X = extremeLayer S

end Lax570090.ConvexLayers
end
