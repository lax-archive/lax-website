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

/-- **The address of an element**: the initial segment it cuts, which is where
the element's input symbol is written. -/
def WMDown (Le : α → α → Prop) (s : α → Prop) (x : α) : Prop := ∀ y, s y ↔ Le y x

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

/-- The order on the elements of the instance. -/
abbrev wmLe : wide.Relations 2 := .wle

/-- The transition symbol. -/
abbrev wmTr : wide.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev wmStart : wide.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev wmAcc : wide.Relations 1 := .acc

/-- The blank symbol. -/
abbrev wmBlank : wide.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev wmRight : wide.Relations 1 := .right

/-- The transition-source symbol. -/
abbrev wmSrc : wide.Relations 2 := .src

/-- The transition-read symbol. -/
abbrev wmRead : wide.Relations 2 := .read

/-- The transition-destination symbol. -/
abbrev wmDst : wide.Relations 2 := .dst

/-- The transition-write symbol. -/
abbrev wmWrite : wide.Relations 2 := .write

/-- The input symbol. -/
abbrev wmInp : wide.Relations 2 := .inp

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wide.Structure A]

/-- The order on the elements of the instance. -/
def WMLe (a b : A) : Prop := RelMap wmLe ![a, b]

/-- Being a transition. -/
def WMTr (a : A) : Prop := RelMap wmTr ![a]

/-- Being a start state. -/
def WMStart (a : A) : Prop := RelMap wmStart ![a]

/-- Being an accepting state. -/
def WMAcc (a : A) : Prop := RelMap wmAcc ![a]

/-- Being the blank symbol. -/
def WMBlank (a : A) : Prop := RelMap wmBlank ![a]

/-- Moving the head right. -/
def WMRight (a : A) : Prop := RelMap wmRight ![a]

/-- The state a transition applies in. -/
def WMSrc (a b : A) : Prop := RelMap wmSrc ![a, b]

/-- The symbol a transition reads. -/
def WMRead (a b : A) : Prop := RelMap wmRead ![a, b]

/-- The state a transition moves to. -/
def WMDst (a b : A) : Prop := RelMap wmDst ![a, b]

/-- The symbol a transition writes. -/
def WMWrite (a b : A) : Prop := RelMap wmWrite ![a, b]

/-- The input at an initial-segment address. -/
def WMInp (a b : A) : Prop := RelMap wmInp ![a, b]

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

/-- The order on the universe: addresses first, in the binary-number order they
inherit from the instance's own order, then the control elements in that same
order. -/
def wpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WMLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WMLe x y

/-- A mark of the control, read on the universe of the machine: no address
carries it. -/
def wpMark (R : A → Prop) : WPoint A → Prop
  | Sum.inl _ => False
  | Sum.inr x => R x

/-- A binary attribute of the control, read on the universe of the machine. -/
def wpAttr (R : A → A → Prop) : WPoint A → WPoint A → Prop
  | Sum.inr x, Sum.inr y => R x y
  | _, _ => False

/-- The initial tape: the address cutting the initial segment of `x` holds the
input symbol of `x`. -/
def wpInp : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMDown WMLe s x ∧ WMInp x y
  | _, _ => False

variable (A) in
/-- **The wide machine an instance describes**: the control read off the
instance, the positions being the addresses. -/
def wideData : TMData (WPoint A) where
  Posn := wpPosn
  Le := wpLe
  Tr := wpMark WMTr
  Start := wpMark WMStart
  Acc := wpMark WMAcc
  Blank := wpMark WMBlank
  Right := wpMark WMRight
  Src := wpAttr WMSrc
  Read := wpAttr WMRead
  Dst := wpAttr WMDst
  Write := wpAttr WMWrite
  Inp := wpInp

end Machine

open FirstOrder

open Language Structure

section RegCell

variable {A : Type} [wide.Structure A]

end RegCell

open Lax904597.Problems Lax485149.Problems

end Lax822549.WideMachines
end
