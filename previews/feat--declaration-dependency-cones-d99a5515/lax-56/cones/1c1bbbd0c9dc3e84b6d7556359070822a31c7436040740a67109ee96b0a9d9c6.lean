-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- Lax56.Geometry
section
namespace Lax56.Geometry

/-- The real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

end Lax56.Geometry
end

-- Lax56.ConvexLayers
section
namespace Lax56.ConvexLayers.remainder
end Lax56.ConvexLayers.remainder

namespace Lax56.ConvexLayers

open Lax56.Geometry

open scoped Classical

/-- All ambient points in the convex hull of `A`, not just its interior points. -/
noncomputable def hullClosure (P A : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ convexHull ℝ (A : Set Point))

end Lax56.ConvexLayers
end
