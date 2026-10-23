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
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax366625.CountingProblems
section
namespace Lax366625
end Lax366625

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingProblems.CountingProblem
end Lax366625.CountingProblems.CountingProblem

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun
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

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A configuration: the current state, the position of the head, and the
contents of the tape. -/
@[ext]
structure Config (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : A
  /-- The symbol in each cell. -/
  tape : A → A

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

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Being an initial configuration: a start state, the head on the lowest
position, and an initial tape. -/
def IsInit (c : Config A) : Prop :=
  M.Start c.state ∧ MinPos M.Le M.Posn c.head ∧ ∀ p, M.InitTape p (c.tape p)

/-- One step: some transition applies in the current state to the symbol under
the head; it writes in that cell, changes state, and moves the head to the
neighboring position in the direction it names. Other cells are unchanged,
and a move off the end of the tape is impossible, so the run stops there. -/
def Step (c c' : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

/-- Reaching one configuration from another in exactly `n` steps. -/
def StepsIn : ℕ → Config A → Config A → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, M.Step c d ∧ StepsIn n d c'

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

/-- The position symbol. -/
abbrev tmPosn : turing.Relations 1 := .posn

/-- The transition symbol. -/
abbrev tmTr : turing.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev tmStart : turing.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev tmAcc : turing.Relations 1 := .acc

/-- The blank symbol. -/
abbrev tmBlank : turing.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev tmRight : turing.Relations 1 := .right

/-- The order symbol. -/
abbrev tmLe : turing.Relations 2 := .le

/-- The transition-source symbol. -/
abbrev tmSrc : turing.Relations 2 := .tsrc

/-- The transition-read symbol. -/
abbrev tmRead : turing.Relations 2 := .tread

/-- The transition-destination symbol. -/
abbrev tmDst : turing.Relations 2 := .tdst

/-- The transition-write symbol. -/
abbrev tmWrite : turing.Relations 2 := .twrite

/-- The input symbol. -/
abbrev tmInp : turing.Relations 2 := .inp

section Shorthands

variable [turing.Structure A]

/-- Being a position. -/
def TMPosn (a : A) : Prop := RelMap tmPosn ![a]

/-- Being a transition. -/
def TMTr (a : A) : Prop := RelMap tmTr ![a]

/-- Being a start state. -/
def TMStart (a : A) : Prop := RelMap tmStart ![a]

/-- Being an accepting state. -/
def TMAcc (a : A) : Prop := RelMap tmAcc ![a]

/-- Being the blank symbol. -/
def TMBlank (a : A) : Prop := RelMap tmBlank ![a]

/-- Moving the head right. -/
def TMRight (a : A) : Prop := RelMap tmRight ![a]

/-- The order on positions. -/
def TMLe (a b : A) : Prop := RelMap tmLe ![a, b]

/-- The state a transition applies in. -/
def TMSrc (a b : A) : Prop := RelMap tmSrc ![a, b]

/-- The symbol a transition reads. -/
def TMRead (a b : A) : Prop := RelMap tmRead ![a, b]

/-- The state a transition moves to. -/
def TMDst (a b : A) : Prop := RelMap tmDst ![a, b]

/-- The symbol a transition writes. -/
def TMWrite (a b : A) : Prop := RelMap tmWrite ![a, b]

/-- The initial contents of a cell. -/
def TMInp (a b : A) : Prop := RelMap tmInp ![a, b]

end Shorthands

/-- The machine an instance describes. -/
def tmData (A : Type) [turing.Structure A] : TMData A where
  Posn := TMPosn
  Le := TMLe
  Tr := TMTr
  Start := TMStart
  Acc := TMAcc
  Blank := TMBlank
  Right := TMRight
  Src := TMSrc
  Read := TMRead
  Dst := TMDst
  Write := TMWrite
  Inp := TMInp

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

-- Lax366625.MachineNumbers
section
namespace Lax366625.MachineNumbers

open Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

end Ripple

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive tapeOutRel : ℕ → Type where
/-- `out p`: the cell `p` is an output cell, holding one digit. -/
  | out : tapeOutRel 1
/-- `one a`: the symbol `a` is read as the digit `1`. -/
  | one : tapeOutRel 1
  deriving DecidableEq

/-- The symbols reading a number off the tape of a machine. -/
def tapeOut : FirstOrder.Language :=
  ⟨fun _ => Empty, tapeOutRel⟩

/-- `out p`: the cell `p` is an output cell, holding one digit. -/
abbrev tpOut : tapeOut.Relations 1 :=
  .out

/-- `one a`: the symbol `a` is read as the digit `1`. -/
abbrev tpOne : tapeOut.Relations 1 :=
  .one

/-- The relational language of machines writing a number. -/
abbrev turingOut : Language.{0, 0} := turing.sum tapeOut

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : TMData A)

/-- **The machine halts in the configuration `c`**: `c` is reached from an
initial configuration within the clock, and no step is possible from it. -/
def Halts (c : Config A) : Prop :=
  ∃ (c₀ : Config A) (n : ℕ), M.IsInit c₀ ∧ n < Nat.card {p : A // M.Posn p} ∧
    M.StepsIn n c₀ c ∧ ∀ e, ¬M.Step c e

end TMData

/-- “Is an output cell”, in the vocabulary of machines writing a number. -/
abbrev mnOut : turingOut.Relations 1 := Sum.inr tpOut

/-- “Is read as the digit `1`”, in the vocabulary of machines writing a
number. -/
abbrev mnOne : turingOut.Relations 1 := Sum.inr tpOne

/-- A machine writing a number is a machine. -/
instance turingOutStructure (A : Type) [turingOut.Structure A] :
    turing.Structure A :=
  (LHom.sumInl : turing →ᴸ turingOut).reduct A

section Semantics

variable {A : Type} [turingOut.Structure A]

/-- The output cell `p` holds the digit `1` when the machine halts, in an
accepting state. -/
def OutDigit (p : A) : Prop :=
  RelMap mnOut ![p] ∧ ∃ c : Config A, TMData.Halts (tmData A) c ∧ (tmData A).Acc c.state ∧
    RelMap mnOne ![c.tape p]

end Semantics

open Lax366625.CountingProblems

end Lax366625.MachineNumbers
end
