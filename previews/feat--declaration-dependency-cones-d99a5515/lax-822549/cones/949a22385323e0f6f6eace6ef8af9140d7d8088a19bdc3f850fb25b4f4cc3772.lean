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
namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.TMData
end Lax904597.Machines.TMData

namespace Lax904597.Machines.turingRel
end Lax904597.Machines.turingRel

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines.turingRel.acc
end Lax904597.Machines.turingRel.acc

namespace Lax904597.Machines.turingRel.blank
end Lax904597.Machines.turingRel.blank

namespace Lax904597.Machines.turingRel.inp
end Lax904597.Machines.turingRel.inp

namespace Lax904597.Machines.turingRel.le
end Lax904597.Machines.turingRel.le

namespace Lax904597.Machines.turingRel.posn
end Lax904597.Machines.turingRel.posn

namespace Lax904597.Machines.turingRel.right
end Lax904597.Machines.turingRel.right

namespace Lax904597.Machines.turingRel.start
end Lax904597.Machines.turingRel.start

namespace Lax904597.Machines.turingRel.tdst
end Lax904597.Machines.turingRel.tdst

namespace Lax904597.Machines.turingRel.tr
end Lax904597.Machines.turingRel.tr

namespace Lax904597.Machines.turingRel.tread
end Lax904597.Machines.turingRel.tread

namespace Lax904597.Machines.turingRel.tsrc
end Lax904597.Machines.turingRel.tsrc

namespace Lax904597.Machines.turingRel.twrite
end Lax904597.Machines.turingRel.twrite
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
namespace Lax822549.WideMachines.wpAttr
end Lax822549.WideMachines.wpAttr

namespace Lax822549.WideMachines.wpInp
end Lax822549.WideMachines.wpInp

namespace Lax822549.WideMachines.wpLe
end Lax822549.WideMachines.wpLe

namespace Lax822549.WideMachines.wpPosn
end Lax822549.WideMachines.wpPosn

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
namespace Lax822549.WideTilings.wtpFirst
end Lax822549.WideTilings.wtpFirst

namespace Lax822549.WideTilings.wtpPosn
end Lax822549.WideTilings.wtpPosn

namespace Lax822549.WideTilings

open Lax822549.WideMachines Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

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

open FirstOrder

open Language Structure

variable {A : Type} (T : TileData A)

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

/-- The order on the elements of the instance. -/
abbrev wtLe : wtile.Relations 2 := .wle

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wtile.Structure A]

/-- The order on the elements. -/
def WTLe (a b : A) : Prop := RelMap wtLe ![a, b]

end Shorthands

section System

variable {A : Type} [wtile.Structure A]

/-- The order on the universe of the tiling: addresses first, in the
binary-number order they inherit from the instance's own order, then the tiles
in that same order. -/
def wtpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WTLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WTLe x y

end System

open Lax904597.Problems Lax485149.Problems

end Lax822549.WideTilings
end
