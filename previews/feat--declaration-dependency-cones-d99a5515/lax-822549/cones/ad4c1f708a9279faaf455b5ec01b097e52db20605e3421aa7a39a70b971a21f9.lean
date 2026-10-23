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
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax485149.Problems
section
namespace Lax485149.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax485149.Problems
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

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

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
namespace Lax822549.WideMachines.wpInp
end Lax822549.WideMachines.wpInp

namespace Lax822549.WideMachines.wpLe
end Lax822549.WideMachines.wpLe

namespace Lax822549.WideMachines

open Lax904597.Machines

open FirstOrder

open Language Structure

section Addresses

variable {α : Type}

/-- **The binary-number order on addresses**: the two subsets agree, or, at some
element where the first is out and the second in, they agree at every strictly
smaller element. Written with the strict order spelled out as
`Le y x ∧ ¬ Le x y`, which is the shape the defining sentence of the expansion
realizes to. -/
def WMSetLe (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  (∀ x, s x ↔ t x) ∨
    ∃ x, (∀ y, (Le y x ∧ ¬Le x y) → (s y ↔ t y)) ∧ ¬s x ∧ t x

/-- **The cell of an element on a file**: the initial segment it cuts among the
elements the file has a register for. The wide machine's register channel and
the wide tiling's bottom row are both described at these addresses – a *file* of
cells rather than the ruler of all the segments. -/
def WMFileSeg (Le : α → α → Prop) (Has : α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∀ y, s y ↔ (Le y x ∧ Has y)

end Addresses

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide-machine instances: the control of
`FirstOrder.Language.turing`, with the positions and their order replaced by an
order on the elements – the digits of an address. -/
inductive wideRel : ℕ → Type
  /-- `wmLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wideRel 2
  /-- `wmTr τ`: `τ` is a transition. -/
  | tr : wideRel 1
  /-- `wmStart q`: `q` is a start state. -/
  | start : wideRel 1
  /-- `wmAcc q`: `q` is an accepting state. -/
  | acc : wideRel 1
  /-- `wmBlank a`: `a` is the blank symbol. -/
  | blank : wideRel 1
  /-- `wmRight τ`: the transition `τ` moves the head right. -/
  | right : wideRel 1
  /-- `wmSrc τ q`: `τ` applies in the state `q`. -/
  | src : wideRel 2
  /-- `wmRead τ a`: `τ` applies when reading the symbol `a`. -/
  | read : wideRel 2
  /-- `wmDst τ q`: `τ` moves to the state `q`. -/
  | dst : wideRel 2
  /-- `wmWrite τ a`: `τ` writes the symbol `a`. -/
  | write : wideRel 2
  /-- `wmInp x a`: the address `{y | y ≤ x}` initially holds the symbol `a`. -/
  | inp : wideRel 2
  deriving DecidableEq

/-- The relational vocabulary of wide-machine instances. -/
def wide : Language :=
  ⟨fun _ => Empty, wideRel⟩

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wide.Structure A]

end Shorthands

section Machine

variable (A : Type)

/-- **The universe of a wide machine**: the addresses – the subsets of the
instance, which are its tape cells and its time steps – together with the
elements of the instance, which are its control. An `abbrev`, so that the sum
structure stays visible to `rw` and to the elaborator. -/
abbrev WPoint : Type := (A → Prop) ⊕ A

variable {A} [wide.Structure A]

/-- Being a position: the addresses are the positions, the control elements are
not. -/
def wpPosn : WPoint A → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- A mark of the control, read on the universe of the machine: no address
carries it. -/
def wpMark (R : A → Prop) : WPoint A → Prop
  | Sum.inl _ => False
  | Sum.inr x => R x

/-- A binary attribute of the control, read on the universe of the machine. -/
def wpAttr (R : A → A → Prop) : WPoint A → WPoint A → Prop
  | Sum.inr x, Sum.inr y => R x y
  | _, _ => False

end Machine

open FirstOrder

open Language Structure

section RegCell

variable {A : Type} [wide.Structure A]

end RegCell

open Lax904597.Problems Lax485149.Problems

end Lax822549.WideMachines
end

-- Lax822549.WideTilings
section
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

/-- **Well-formedness**, folded into the yes-instances exactly as
`TMData.WellFormed` is: the order is linear, and there is
a position to index the grid by. -/
def WellFormed : Prop := IsLinOrd T.Le ∧ ∃ p, T.Posn p

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

instance instIsRelationalWtile : wtile.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

/-- The order on the elements of the instance. -/
abbrev wtLe : wtile.Relations 2 := .wle

/-- The digit symbol. -/
abbrev wtDig : wtile.Relations 1 := .dig

/-- The tile symbol. -/
abbrev wtTile : wtile.Relations 1 := .tile

/-- The accepting-tile symbol. -/
abbrev wtAcc : wtile.Relations 1 := .tacc

/-- The horizontal-compatibility symbol. -/
abbrev wtHoriz : wtile.Relations 2 := .horiz

/-- The vertical-compatibility symbol. -/
abbrev wtVert : wtile.Relations 2 := .vert

/-- The bottom-row symbol. -/
abbrev wtFirst : wtile.Relations 2 := .first

/-- The base-tile symbol. -/
abbrev wtBase : wtile.Relations 1 := .base

/-- The start-tile symbol. -/
abbrev wtStart : wtile.Relations 1 := .tstart

/-- The left-edge symbol. -/
abbrev wtEdgeL : wtile.Relations 1 := .ledge

/-- The right-edge symbol. -/
abbrev wtEdgeR : wtile.Relations 1 := .redge

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wtile.Structure A]

/-- The order on the elements. -/
def WTLe (a b : A) : Prop := RelMap wtLe ![a, b]

/-- Being a digit: one of the elements the grid's coordinates are subsets of. -/
def WTDig (a : A) : Prop := RelMap wtDig ![a]

/-- Being a tile. -/
def WTTile (a : A) : Prop := RelMap wtTile ![a]

/-- Being an accepting tile. -/
def WTAcc (a : A) : Prop := RelMap wtAcc ![a]

/-- Horizontal compatibility. -/
def WTHoriz (a b : A) : Prop := RelMap wtHoriz ![a, b]

/-- Vertical compatibility. -/
def WTVert (a b : A) : Prop := RelMap wtVert ![a, b]

/-- The bottom row, at the cell of an element. -/
def WTFirst (a b : A) : Prop := RelMap wtFirst ![a, b]

/-- Being a base tile. -/
def WTBase (a : A) : Prop := RelMap wtBase ![a]

/-- Being a start tile. -/
def WTStart (a : A) : Prop := RelMap wtStart ![a]

/-- Being a left-edge tile: one the leftmost column may carry. -/
def WTEdgeL (a : A) : Prop := RelMap wtEdgeL ![a]

/-- Being a right-edge tile: one the rightmost column may carry. -/
def WTEdgeR (a : A) : Prop := RelMap wtEdgeR ![a]

/-- **An element the bottom row is described at**: one whose cell carries a
tile. These are the elements the file has cells for. -/
def WTHasFirst (a : A) : Prop := ∃ t : A, WTFirst a t

end Shorthands

section System

variable {A : Type} [wtile.Structure A]

/-- Being a position: an address is one exactly when it holds digits alone, so
the grid is indexed by the subsets of the *marked* part of the instance. That is
what leaves the instance room for its tiles: a tile is an element like any
other, and only the digits are coordinates. -/
def wtpPosn : WPoint A → Prop
  | Sum.inl s => ∀ x, s x → WTDig x
  | Sum.inr _ => False

/-- The order on the universe of the tiling: addresses first, in the
binary-number order they inherit from the instance's own order, then the tiles
in that same order. -/
def wtpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WTLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WTLe x y

/-- The bottom row: the cell of `x` – the segment `x` cuts among the elements
the description names – may carry the tiles of `x`, and every other address a
base tile. That is the same device as the register channel's input
(`wpInpReg`): a file of cells, not the ruler of all the
segments, because a clocked machine's tape is described the same way and that is
where this problem's hardness comes from. -/
def wtpFirst : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMFileSeg WTLe WTHasFirst s x ∧ WTFirst x y
  | _, _ => False

variable (A) in
/-- **The wide tile system an instance describes**: the tiles read off the
instance, the positions being the addresses. -/
def wideTileData : TileData (WPoint A) where
  Posn := wtpPosn
  Le := wtpLe
  Tile := wpMark WTTile
  Acc := wpMark WTAcc
  Horiz := wpAttr WTHoriz
  Vert := wpAttr WTVert
  First := wtpFirst
  Base := wpMark WTBase
  Start := wpMark WTStart
  EdgeL := wpMark WTEdgeL
  EdgeR := wpMark WTEdgeR

end System

open Lax904597.Problems Lax485149.Problems

/-- **Corridor tiling one exponential up.** -/
def WideCorridor : DecisionProblem wtile :=
  DecisionProblem.ofPred fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).CorridorTileable

end Lax822549.WideTilings
end
