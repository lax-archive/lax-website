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

/-- The internal vertices of `P` avoid `X`. -/
def InternallyAvoids {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (X : Finset V) : Prop :=
  ∀ v ∈ P.vertices, v ∈ X → v = P.source ∨ v = P.target

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

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
namespace Lax17.Crossbar

universe u

open Lax17.Paths

/-- The parameter is an integral power of two. -/
def IsPowerOfTwo (g : ℕ) : Prop :=
  ∃ exponent : ℕ, g = 2 ^ exponent

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

/-- A depth-`D` pseudo-grid with `κ` main rows at scale `g`. -/
structure PseudoGrid {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V)
    (g D κ : ℕ) where
  RowIndex : Type
  [rowFintype : Fintype RowIndex]
  [rowDecidableEq : DecidableEq RowIndex]
  row_count : Fintype.card RowIndex = κ
  row : RowIndex → Path G
  row_connects : ∀ i : RowIndex, (row i).Connects A B
  rows_disjoint :
    Pairwise fun i j => Disjoint (row i).vertices (row j).vertices
  depth_pos : 0 < D
  reserved : Fin D → Finset RowIndex
  reserved_card_le :
    ∀ i : Fin D, (reserved i).card ≤ g ^ 2
  reserved_disjoint :
    ∀ ⦃i j : Fin D⦄, i ≠ j →
      Disjoint (reserved i) (reserved j)
  ColumnIndex : Type
  [columnFintype : Fintype ColumnIndex]
  [columnDecidableEq : DecidableEq ColumnIndex]
  column_count : Fintype.card ColumnIndex = κ / 4
  column : ColumnIndex → Path G
  columns_disjoint :
    Pairwise fun i j => Disjoint (column i).vertices (column j).vertices
  column_reaches_X_cleanly :
    ∀ j : ColumnIndex,
      ((column j).source ∈ X ∨ (column j).target ∈ X) ∧
        (column j).InternallyAvoids X
  unreserved_row_avoids_columns :
    ∀ p : RowIndex,
      (∀ i : Fin D, p ∉ reserved i) →
        ∀ j : ColumnIndex,
          Disjoint (row p).vertices (column j).vertices
  few_columns_miss_reserved :
    ∀ i : Fin D,
      ∃ miss : Finset ColumnIndex,
        miss.card ≤ 2 * g ^ 2 ∧
          ∀ j : ColumnIndex, j ∉ miss →
            ∃ p ∈ reserved i,
              ¬ Disjoint (row p).vertices (column j).vertices

end Lax17.Crossbar
end

-- Lax17.Degree
section
namespace Lax17.Degree

universe u

/-- `N` is the neighbourhood of `v` in `G`. -/
def IsNeighbourhood {V : Type u} (G : SimpleGraph V) (v : V)
    (N : Finset V) : Prop :=
  ∀ w : V, w ∈ N ↔ G.Adj v w

/-- The degree of `v` in `G` is exactly `d`. -/
def Exactly {V : Type u} (G : SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighbourhood G v N ∧ N.card = d

end Lax17.Degree
end

-- Lax17.CrossbarOrPseudoGrid
section
namespace Lax17.CrossbarOrPseudoGrid

universe u

/-- The self-contained crossbar-or-pseudo-grid form of Theorem 4.1. -/
axiom crossbarOrPseudoGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B X : Finset V} {g κ D : ℕ},
      2 ≤ g →
        Lax17.Crossbar.IsPowerOfTwo g →
          A.card = κ → B.card = κ → X.card = κ →
            Disjoint A B → Disjoint A X → Disjoint B X →
              (∀ x ∈ X, Lax17.Degree.Exactly G x 1) →
                Lax17.Paths.VertexLinkage G A B κ →
                  Lax17.Paths.VertexLinkage G A X κ →
                    1 ≤ D → D ≤ κ / (2 * g ^ 2) →
                      Nonempty
                          (Lax17.Crossbar.System G A B X (g ^ 2)) ∨
                        Nonempty
                          (Lax17.Crossbar.PseudoGrid
                            G A B X g D κ)

end Lax17.CrossbarOrPseudoGrid
end
