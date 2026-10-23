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
namespace Lax570090.ConvexLayers

open Lax570090.Geometry

open scoped Classical

/-- Vertices of the convex hull, including all points of sets of size at most two. -/
noncomputable def extremeLayer (P : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ)

/-- The remainder after deleting the current outer layer. -/
noncomputable def inner (P : Finset Point) : Finset Point := P \ extremeLayer P

/-- The remainder after `n` layers have been removed. -/
noncomputable def remainder (P : Finset Point) : ℕ → Finset Point
  | 0 => P
  | n + 1 => inner (remainder P n)

end Lax570090.ConvexLayers
end
