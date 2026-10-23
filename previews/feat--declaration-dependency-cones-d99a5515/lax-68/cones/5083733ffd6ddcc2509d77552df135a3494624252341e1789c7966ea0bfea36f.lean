-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
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

def HasStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (StraightLineDrawing G)

end Lax68.StraightLineDrawings
end

-- Lax68.Planar
section
set_option autoImplicit false

namespace Lax68.Planar

/-- Existence of a crossing-free straight-line drawing in the real plane. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  StraightLineDrawings.HasStraightLineDrawing G

end Lax68.Planar
end

-- Lax68.Stars
section
set_option autoImplicit false

namespace Lax68.Stars

def HasStarShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ centre : V,
    centre ∈ G.universalVerts ∧
    ∀ ⦃u v⦄, G.Adj u v → u = centre ∨ v = centre

def IsStar {V : Type*} (G : SimpleGraph V) : Prop :=
  HasStarShape G

end Lax68.Stars
end

-- Lax68.StarPlanar
section
set_option autoImplicit false

namespace Lax68.StarPlanar

/-- Every finite star graph is planar. -/
axiom star_planar {V : Type*} [Finite V] {G : SimpleGraph V} :
  Lax68.Stars.IsStar G →
  Lax68.Planar.IsPlanar G

end Lax68.StarPlanar
end
