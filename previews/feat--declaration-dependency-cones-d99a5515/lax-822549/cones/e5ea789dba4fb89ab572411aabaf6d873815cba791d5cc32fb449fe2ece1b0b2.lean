-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax904597.Machines
section
namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
end

-- Lax535992.DeterministicMachines
section
namespace Lax535992
end Lax535992

namespace Lax535992.DeterministicMachines
end Lax535992.DeterministicMachines

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData
end

-- Lax134656.SpaceBoundedMachines
section
namespace Lax134656
end Lax134656

namespace Lax134656.SpaceBoundedMachines
end Lax134656.SpaceBoundedMachines

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData
end

-- Lax822549.WideMachines
section
namespace Lax822549
end Lax822549

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax822549.WideMachines.wideRel
end Lax822549.WideMachines.wideRel

namespace Lax822549.WideMachines.wpAttr
end Lax822549.WideMachines.wpAttr

namespace Lax822549.WideMachines.wpInp
end Lax822549.WideMachines.wpInp

namespace Lax822549.WideMachines.wpLe
end Lax822549.WideMachines.wpLe

namespace Lax822549.WideMachines.wpPosn
end Lax822549.WideMachines.wpPosn

namespace Lax822549.WideMachines.wideRel.acc
end Lax822549.WideMachines.wideRel.acc

namespace Lax822549.WideMachines.wideRel.blank
end Lax822549.WideMachines.wideRel.blank

namespace Lax822549.WideMachines.wideRel.dst
end Lax822549.WideMachines.wideRel.dst

namespace Lax822549.WideMachines.wideRel.inp
end Lax822549.WideMachines.wideRel.inp

namespace Lax822549.WideMachines.wideRel.read
end Lax822549.WideMachines.wideRel.read

namespace Lax822549.WideMachines.wideRel.right
end Lax822549.WideMachines.wideRel.right

namespace Lax822549.WideMachines.wideRel.src
end Lax822549.WideMachines.wideRel.src

namespace Lax822549.WideMachines.wideRel.start
end Lax822549.WideMachines.wideRel.start

namespace Lax822549.WideMachines.wideRel.tr
end Lax822549.WideMachines.wideRel.tr

namespace Lax822549.WideMachines.wideRel.wle
end Lax822549.WideMachines.wideRel.wle

namespace Lax822549.WideMachines.wideRel.write
end Lax822549.WideMachines.wideRel.write
end

-- Lax822549.WideTilings
section
namespace Lax822549.WideTilings.wtpFirst
end Lax822549.WideTilings.wtpFirst

namespace Lax822549.WideTilings.wtpLe
end Lax822549.WideTilings.wtpLe

namespace Lax822549.WideTilings.wtpPosn
end Lax822549.WideTilings.wtpPosn

namespace Lax822549.WideTilings

open Lax822549.WideMachines Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

open FirstOrder

open Language Structure

/-- **A tile system**, read off an instance: the positions with their order,
the tiles with their compatibilities, the bottom row and the accepting tiles.
As with `TMData`, the record is a plain bundle of
predicates, so everything about tilings is stated once and read at whatever
structure supplies them. -/
structure TileData (A : Type) where
  /-- Being a position – a column, and equally a row. -/
  Posn : A → Prop
  /-- The order on positions. -/
  Le : A → A → Prop
  /-- Being a tile. -/
  Tile : A → Prop
  /-- Being an accepting tile. -/
  Acc : A → Prop
  /-- The right neighbor may carry this tile. -/
  Horiz : A → A → Prop
  /-- The upper neighbor may carry this tile. -/
  Vert : A → A → Prop
  /-- The bottom row's cell in this column may carry this tile. -/
  First : A → A → Prop
  /-- Being a base tile: what a column the description says nothing about
  carries in the bottom row. -/
  Base : A → Prop
  /-- Being a start tile: what the corner of the grid carries. -/
  Start : A → Prop
  /-- Being a left-edge tile: what the leftmost column may carry. -/
  EdgeL : A → Prop
  /-- Being a right-edge tile: what the rightmost column may carry. -/
  EdgeR : A → Prop

namespace TileData

variable {A : Type} (T : TileData A)

/-- **The tiles the bottom row may carry in a column**: the ones the
description names there, and the base tiles in a column it names none. This is
`TMData.InitTape`'s device – a description of the row
rather than a listing – and it is what lets an expansion carry it. -/
def FirstTile (x t : A) : Prop :=
  T.First x t ∨ ((∀ u, ¬T.First x u) ∧ T.Base t)

open FirstOrder

open Language Structure

variable {A : Type} (T : TileData A)

/-- **A tiling of the corridor up to a given height**: every cell of the strip
carries a tile, the bottom row is one the description allows, the two edge
columns carry tiles allowed there, neighbors in a row and rows one above the
other are compatible, and the top row carries an accepting tile.

The height is where a corridor differs from
`TileData.IsTiling`: nothing in the instance bounds it,
and the tiles above the accepting row are not asked about at all. -/
def IsCorridor (h : ℕ) (τ : ℕ → A → A) : Prop :=
  (∀ k x, k ≤ h → T.Posn x → T.Tile (τ k x)) ∧
    (∀ x, T.Posn x →
      ((MinPos T.Le T.Posn x → T.Start (τ 0 x)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ 0 x)))) ∧
    (∀ k x, k ≤ h → MinPos T.Le T.Posn x → T.EdgeL (τ k x)) ∧
    (∀ k x, k ≤ h → MaxPos T.Le T.Posn x → T.EdgeR (τ k x)) ∧
    (∀ k x x', k ≤ h → SuccPos T.Le T.Posn x x' → T.Horiz (τ k x) (τ k x')) ∧
    (∀ k x, k < h → T.Posn x → T.Vert (τ k x) (τ (k + 1) x)) ∧
    ∃ x, T.Posn x ∧ T.Acc (τ h x)

/-- **The corridor can be tiled**: some assignment of tiles to its cells is a
tiling of it, of some height. -/
def CorridorTileable : Prop := ∃ (h : ℕ) (τ : ℕ → A → A), T.IsCorridor h τ

end TileData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide tile-system instances: the tiles of
`FirstOrder.Language.tiling` with their compatibilities, and the positions and
their order replaced by an order on the elements – the digits of an address. -/
inductive wtileRel : ℕ → Type
  /-- `wtLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wtileRel 2
  /-- `wtDig x`: `x` is a digit – one of the elements the grid's coordinates are
  subsets of. -/
  | dig : wtileRel 1
  /-- `wtTile t`: `t` is a tile. -/
  | tile : wtileRel 1
  /-- `wtAcc t`: `t` is an accepting tile. -/
  | tacc : wtileRel 1
  /-- `wtHoriz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : wtileRel 2
  /-- `wtVert t t'`: `t'` may stand immediately above `t`. -/
  | vert : wtileRel 2
  /-- `wtFirst x t`: the bottom row's cell of `x` may carry `t`. -/
  | first : wtileRel 2
  /-- `wtBase t`: `t` is a base tile – what the bottom row carries where the
  description says nothing. -/
  | base : wtileRel 1
  /-- `wtStart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : wtileRel 1
  /-- `wtEdgeL t`: `t` may stand in the leftmost column. -/
  | ledge : wtileRel 1
  /-- `wtEdgeR t`: `t` may stand in the rightmost column. -/
  | redge : wtileRel 1
  deriving DecidableEq

/-- The relational vocabulary of wide tile-system instances. -/
def wtile : Language :=
  ⟨fun _ => Empty, wtileRel⟩

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wtile.Structure A]

end Shorthands

section System

variable {A : Type} [wtile.Structure A]

end System

open Lax904597.Problems Lax485149.Problems

end Lax822549.WideTilings
end
