-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

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

-- Lax881656.Bipartite
section
set_option autoImplicit false

namespace Lax881656.Bipartite

/-- A simple graph is bipartite when it is properly colorable with two colors. -/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Colorable 2

end Lax881656.Bipartite
end

-- Lax881656.Cubic
section
set_option autoImplicit false

namespace Lax881656.Cubic

/-- A finite simple graph is cubic when every vertex has degree three. -/
def IsCubic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = 3

end Lax881656.Cubic
end

-- Lax881656.HamiltonianCycle
section
set_option autoImplicit false

namespace Lax881656.HamiltonianCycle

/-- A closed walk is a Hamiltonian cycle when it is a cycle and visits every
vertex of the graph. -/
def IsHamiltonianCycle {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {v : V} (cycle : G.Walk v v) : Prop :=
  cycle.IsCycle ∧ ∀ w : V, w ∈ cycle.support

/-- A graph has a Hamiltonian cycle when it contains a spanning cycle. -/
def HasHamiltonianCycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ cycle : G.Walk v v, IsHamiltonianCycle cycle

end Lax881656.HamiltonianCycle
end

-- Lax881656.ThreeConnected
section
set_option autoImplicit false

namespace Lax881656.ThreeConnected

/-- A finite graph is 3-connected if deleting at most two vertices leaves a
connected graph, and the original graph has at least four vertices. -/
def IsThreeConnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected

end Lax881656.ThreeConnected
end

-- Lax881656.BarnetteConjecture
section
set_option autoImplicit false

namespace Lax881656.BarnetteConjecture

/-- Barnette's conjecture: every 3-connected cubic bipartite planar graph has
a Hamiltonian cycle. -/
axiom barnette_conjecture {n : ℕ} (G : SimpleGraph (Fin n)) :
  (Lax881656.ThreeConnected.IsThreeConnected G ∧
    Lax881656.Cubic.IsCubic G ∧
    Lax881656.Bipartite.IsBipartite G ∧
    Lax68.Planar.IsPlanar G) →
  Lax881656.HamiltonianCycle.HasHamiltonianCycle G

end Lax881656.BarnetteConjecture
end
