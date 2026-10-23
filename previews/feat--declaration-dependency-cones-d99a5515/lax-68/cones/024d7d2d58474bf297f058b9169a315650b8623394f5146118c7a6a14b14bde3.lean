-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic

-- Lax68.GraphMinors
section
namespace Lax68
end Lax68

namespace Lax68.GraphMinors
end Lax68.GraphMinors

namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel
end

-- Lax68.StraightLineDrawings
section
set_option autoImplicit false

namespace Lax68.StraightLineDrawings

abbrev Point := ℝ × ℝ

structure StraightLineDrawing {V : Type*} (G : SimpleGraph V) where
  point : V → Point
  injective : Function.Injective point
  noVertexOnEdge :
    ∀ {a b c : V},
      G.Adj a b →
      c ≠ a →
      c ≠ b →
      point c ∉ segment ℝ (point a) (point b)
  disjointEdges :
    ∀ {a b c d : V},
      G.Adj a b →
      G.Adj c d →
      Disjoint ({a, b} : Set V) ({c, d} : Set V) →
      Disjoint
        (segment ℝ (point a) (point b))
        (segment ℝ (point c) (point d))

end Lax68.StraightLineDrawings
end

-- Lax68.Outerplanar
section
set_option autoImplicit false

namespace Lax68.Outerplanar

structure OuterplaneDrawing {V : Type*} (G : SimpleGraph V)
    extends StraightLineDrawings.StraightLineDrawing G where
  radius : ℝ
  radius_pos : 0 < radius
  onBoundary :
    ∀ v : V,
      let p := toStraightLineDrawing.point v
      p.1 ^ 2 + p.2 ^ 2 = radius ^ 2

def IsOuterplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (OuterplaneDrawing G)

end Lax68.Outerplanar
end

-- Lax68.MaximalOuterplanar
section
set_option autoImplicit false

namespace Lax68.MaximalOuterplanar

def IsMaximalOuterplanar {V : Type*}
    (G : SimpleGraph V) : Prop :=
  Outerplanar.IsOuterplanar G ∧
    ∀ H : SimpleGraph V,
      G < H →
      ¬ Outerplanar.IsOuterplanar H

end Lax68.MaximalOuterplanar
end

-- Lax68.Triangles
section
set_option autoImplicit false

namespace Lax68.Triangles

def IsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.completeGraph (Fin 3))

end Lax68.Triangles
end

-- Lax68.TriangleMaximalOuterplanar
section
set_option autoImplicit false

namespace Lax68.TriangleMaximalOuterplanar

/-- Every triangle is maximal outerplanar. -/
axiom triangle_maximalOuterplanar
    {V : Type*} {G : SimpleGraph V} :
  Lax68.Triangles.IsTriangle G →
  Lax68.MaximalOuterplanar.IsMaximalOuterplanar G

end Lax68.TriangleMaximalOuterplanar
end
