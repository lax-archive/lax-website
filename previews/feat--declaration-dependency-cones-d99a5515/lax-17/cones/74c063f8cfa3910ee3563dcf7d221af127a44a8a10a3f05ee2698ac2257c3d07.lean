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

namespace Lax17.Paths.VertexLinkage
end Lax17.Paths.VertexLinkage

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

/-- The finite set of edges used by a path. -/
noncomputable def edges {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

end Path

/-- An edge set meeting every oriented `A`-to-`B` path. -/
def IsEdgeSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (F : Finset (Sym2 V)) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ e ∈ P.edges, e ∈ F

end Lax17.Paths
end
