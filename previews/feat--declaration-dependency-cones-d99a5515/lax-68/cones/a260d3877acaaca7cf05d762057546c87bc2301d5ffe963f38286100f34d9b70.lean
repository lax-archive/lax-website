-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Real.Basic

-- Lax68.Paths
section
set_option autoImplicit false

namespace Lax68.Paths

def HasPathShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ,
    0 < n ∧
    Nonempty (G ≃g SimpleGraph.pathGraph n)

def IsPath {V : Type*} (G : SimpleGraph V) : Prop :=
  HasPathShape G

end Lax68.Paths
end

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

-- Lax68.PathPlanar
section
set_option autoImplicit false

namespace Lax68.PathPlanar

/-- Every path graph is planar. -/
axiom path_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.Paths.IsPath G →
  Lax68.Planar.IsPlanar G

end Lax68.PathPlanar
end
