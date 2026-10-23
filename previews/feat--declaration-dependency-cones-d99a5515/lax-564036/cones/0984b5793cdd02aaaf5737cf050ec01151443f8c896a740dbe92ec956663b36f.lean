-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Finite

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

-- Lax564036.AlternatingMachines
section
namespace Lax564036.AlternatingMachines.guardQ
end Lax564036.AlternatingMachines.guardQ

namespace Lax564036.AlternatingMachines.ATMData.AltAcc
end Lax564036.AlternatingMachines.ATMData.AltAcc

namespace Lax564036.AlternatingMachines

open Lax904597.Problems Lax485149.Problems

open Lax904597.Machines

/-- An alternating Turing machine presented as relations on a universe: a
machine in the sense of `TMData`, together with marks
splitting its states into quantifier blocks. -/
structure ATMData (A : Type) extends TMData A where
  /-- `Blk j q`: the state `q` belongs to the `j`-th quantifier block. -/
  Blk : ℕ → A → Prop

namespace ATMData

variable {A : Type} (M : ATMData A)

end ATMData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of alternating machine instances: those of machine
instances, and one unary mark per quantifier block. -/
inductive turingAltRel (k : ℕ) : ℕ → Type
  /-- A symbol of the underlying machine vocabulary. -/
  | base {n : ℕ} : turingRel n → turingAltRel k n
  /-- `blk i q`: the state `q` belongs to the `i`-th quantifier block. -/
  | blk : Fin k → turingAltRel k 1

/-- The relational vocabulary of alternating machine instances with `k`
quantifier blocks. -/
def turingAlt (k : ℕ) : Language :=
  ⟨fun _ => Empty, turingAltRel k⟩

variable {k : ℕ}

/-- The position symbol. -/
abbrev atmPosn : (turingAlt k).Relations 1 := .base .posn

/-- The transition symbol. -/
abbrev atmTr : (turingAlt k).Relations 1 := .base .tr

/-- The start-state symbol. -/
abbrev atmStart : (turingAlt k).Relations 1 := .base .start

/-- The accepting-state symbol. -/
abbrev atmAcc : (turingAlt k).Relations 1 := .base .acc

/-- The blank symbol. -/
abbrev atmBlank : (turingAlt k).Relations 1 := .base .blank

/-- The move-right symbol. -/
abbrev atmRight : (turingAlt k).Relations 1 := .base .right

/-- The order symbol. -/
abbrev atmLe : (turingAlt k).Relations 2 := .base .le

/-- The transition-source symbol. -/
abbrev atmSrc : (turingAlt k).Relations 2 := .base .tsrc

/-- The transition-read symbol. -/
abbrev atmRead : (turingAlt k).Relations 2 := .base .tread

/-- The transition-destination symbol. -/
abbrev atmDst : (turingAlt k).Relations 2 := .base .tdst

/-- The transition-write symbol. -/
abbrev atmWrite : (turingAlt k).Relations 2 := .base .twrite

/-- The input symbol. -/
abbrev atmInp : (turingAlt k).Relations 2 := .base .inp

/-- The mark of the `i`-th quantifier block. -/
abbrev atmBlk (i : Fin k) : (turingAlt k).Relations 1 := .blk i

open FirstOrder

open Language Structure

section Shorthands

variable {k : ℕ} {A : Type} [(turingAlt k).Structure A]

/-- Being a position. -/
def ATMPosn (a : A) : Prop := RelMap (atmPosn (k := k)) ![a]

/-- Being a transition. -/
def ATMTr (a : A) : Prop := RelMap (atmTr (k := k)) ![a]

/-- Being a start state. -/
def ATMStart (a : A) : Prop := RelMap (atmStart (k := k)) ![a]

/-- Being an accepting state. -/
def ATMAcc (a : A) : Prop := RelMap (atmAcc (k := k)) ![a]

/-- Being the blank symbol. -/
def ATMBlank (a : A) : Prop := RelMap (atmBlank (k := k)) ![a]

/-- Moving the head right. -/
def ATMRight (a : A) : Prop := RelMap (atmRight (k := k)) ![a]

/-- The order on positions. -/
def ATMLe (a b : A) : Prop := RelMap (atmLe (k := k)) ![a, b]

/-- The state a transition applies in. -/
def ATMSrc (a b : A) : Prop := RelMap (atmSrc (k := k)) ![a, b]

/-- The symbol a transition reads. -/
def ATMRead (a b : A) : Prop := RelMap (atmRead (k := k)) ![a, b]

/-- The state a transition moves to. -/
def ATMDst (a b : A) : Prop := RelMap (atmDst (k := k)) ![a, b]

/-- The symbol a transition writes. -/
def ATMWrite (a b : A) : Prop := RelMap (atmWrite (k := k)) ![a, b]

/-- The initial contents of a cell. -/
def ATMInp (a b : A) : Prop := RelMap (atmInp (k := k)) ![a, b]

/-- The block of a state, read off the marks: the marks of the vocabulary are
indexed by `Fin k`, so a block index beyond `k` marks nothing. -/
def ATMBlk (j : ℕ) (a : A) : Prop := ∃ h : j < k, RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a]

/-- The alternating machine an instance describes. -/
def atmData (k : ℕ) (A : Type) [(turingAlt k).Structure A] : ATMData A where
  Posn := ATMPosn (k := k)
  Le := ATMLe (k := k)
  Tr := ATMTr (k := k)
  Start := ATMStart (k := k)
  Acc := ATMAcc (k := k)
  Blank := ATMBlank (k := k)
  Right := ATMRight (k := k)
  Src := ATMSrc (k := k)
  Read := ATMRead (k := k)
  Dst := ATMDst (k := k)
  Write := ATMWrite (k := k)
  Inp := ATMInp (k := k)
  Blk := ATMBlk (k := k)

end Shorthands

end Lax564036.AlternatingMachines
end
