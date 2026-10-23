-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

-- Lax68.SeriesParallel
section
set_option autoImplicit false

namespace Lax68.SeriesParallel

def edgeGraph {V : Type*} (s t : V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    (u = s ∧ v = t) ∨
    (u = t ∧ v = s)

inductive TwoTerminal {V : Type*} : SimpleGraph V → V → V → Prop
  | edge (s t : V) (hne : s ≠ t) :
      TwoTerminal (edgeGraph s t) s t
  | series
      {G H : SimpleGraph V}
      {s m t : V}
      (left : TwoTerminal G s m)
      (right : TwoTerminal H m t)
      (meet :
        ∀ v,
          v ∈ G.support →
          v ∈ H.support →
          v = m) :
      TwoTerminal (G ⊔ H) s t
  | parallel
      {G H : SimpleGraph V}
      {s t : V}
      (left : TwoTerminal G s t)
      (right : TwoTerminal H s t)
      (meet :
        ∀ v,
          v ∈ G.support →
          v ∈ H.support →
          v = s ∨ v = t) :
      TwoTerminal (G ⊔ H) s t

def IsSeriesParallel {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ s t,
    TwoTerminal G s t ∧
    G.support = Set.univ

end Lax68.SeriesParallel
end

-- Lax68.SeriesParallelPlanar
section
set_option autoImplicit false

namespace Lax68.SeriesParallelPlanar

/-- Every series-parallel graph is planar.

Open in this formalization: no proof is supplied yet. -/
axiom seriesParallel_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.SeriesParallel.IsSeriesParallel G →
  Lax68.Planar.IsPlanar G

end Lax68.SeriesParallelPlanar
end
