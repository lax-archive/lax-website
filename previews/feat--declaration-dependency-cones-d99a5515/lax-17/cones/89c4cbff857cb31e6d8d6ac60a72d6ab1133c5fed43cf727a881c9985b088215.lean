-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

-- Lax17.Paths
section
namespace Lax17.Paths.EdgeCutPartition
end Lax17.Paths.EdgeCutPartition

namespace Lax17.Paths.EdgeLinkage
end Lax17.Paths.EdgeLinkage

namespace Lax17.Paths.VertexLinkage.BridgeBetween
end Lax17.Paths.VertexLinkage.BridgeBetween

namespace Lax17.Paths

universe u

/-- A simple finite path in `G`, with its orientation recorded. -/
structure Path {V : Type u} (G : SimpleGraph V) where
  source : V
  target : V
  walk : G.Walk source target
  simple : walk.IsPath

namespace Path

/-- The finite set of vertices used by a path. -/
noncomputable def vertices {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset V :=
  P.walk.support.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

/-- A vertex set meeting every oriented `A`-to-`B` path. -/
def IsVertexSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ v ∈ P.vertices, v ∈ X

end Lax17.Paths
end

-- Lax17.VertexMenger
section
namespace Lax17.VertexMenger

universe u

/-- Finite vertex-Menger in packing-or-separator form. -/
axiom vertexMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ),
      Nonempty (Lax17.Paths.VertexLinkage G A B k) ∨
        ∃ X : Finset V,
          X.card < k ∧ Lax17.Paths.IsVertexSeparator G A B X

end Lax17.VertexMenger
end
