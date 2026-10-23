-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

-- Lax17.Minor
section
namespace Lax17
end Lax17

namespace Lax17.Minor
end Lax17.Minor

namespace Lax17.Minor.Model
end Lax17.Minor.Model
end

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

/-- The finite set of vertices used by a path. -/
noncomputable def vertices {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset V :=
  P.walk.support.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

end Path

end Lax17.Paths
end

-- Lax17.Linkedness
section
namespace Lax17.Linkedness
end Lax17.Linkedness
end

-- Lax17.PathOfSets
section
namespace Lax17.PathOfSets
end Lax17.PathOfSets

namespace Lax17.PathOfSets.HairyClusterSplit
end Lax17.PathOfSets.HairyClusterSplit

namespace Lax17.PathOfSets.HairySystem
end Lax17.PathOfSets.HairySystem

namespace Lax17.PathOfSets.StrongSystem
end Lax17.PathOfSets.StrongSystem

namespace Lax17.PathOfSets.System
end Lax17.PathOfSets.System

namespace Lax17.PathOfSets.ThreeWayClusterSplit
end Lax17.PathOfSets.ThreeWayClusterSplit
end

-- Lax17.Crossbar
section
namespace Lax17.Crossbar.PseudoGrid
end Lax17.Crossbar.PseudoGrid

namespace Lax17.Crossbar

universe u

open Lax17.Paths

/-- A crossbar of width `ρ`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) (ρ : ℕ) where
  mainPath : Fin ρ → Path G
  main_connects : ∀ i : Fin ρ, (mainPath i).Connects A B
  main_disjoint :
    Pairwise fun i j => Disjoint (mainPath i).vertices (mainPath j).vertices
  spokePath : Fin ρ → Path G
  spoke_disjoint :
    Pairwise fun i j => Disjoint (spokePath i).vertices (spokePath j).vertices
  attachment : Fin ρ → V
  attachment_on_main :
    ∀ i : Fin ρ, attachment i ∈ (mainPath i).vertices
  attachment_on_spoke :
    ∀ i : Fin ρ, attachment i ∈ (spokePath i).vertices
  exact_attachment :
    ∀ i : Fin ρ,
      (mainPath i).vertices ∩ (spokePath i).vertices = {attachment i}
  exit : Fin ρ → V
  attachment_is_endpoint :
    ∀ i : Fin ρ,
      attachment i = (spokePath i).source ∨
        attachment i = (spokePath i).target
  exit_is_other_endpoint :
    ∀ i : Fin ρ,
      exit i =
        if (spokePath i).source = attachment i then
          (spokePath i).target
        else
          (spokePath i).source
  exit_in_X : ∀ i : Fin ρ, exit i ∈ X
  exit_off_main :
    ∀ i : Fin ρ, exit i ∉ (mainPath i).vertices
  spoke_avoids_other_main :
    ∀ ⦃i j : Fin ρ⦄, i ≠ j →
      Disjoint (spokePath i).vertices (mainPath j).vertices

end Lax17.Crossbar
end
