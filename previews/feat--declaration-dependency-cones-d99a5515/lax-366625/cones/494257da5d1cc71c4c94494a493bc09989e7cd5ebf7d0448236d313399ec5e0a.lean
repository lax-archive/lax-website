-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
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
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

/-- The counting problem given by a number attached to every structure: the
least value it takes on the structures isomorphic to a given one, which is
invariant by construction. When the number is itself invariant, this is the
number. -/
noncomputable def ofFun (f : ∀ (A : Type) [L.Structure A], ℕ) : CountingProblem L where
  Count := fun A _ =>
    sInf {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n}
  iso_invariant := fun e =>
    congrArg sInf (Set.ext fun _ =>
      ⟨fun ⟨B, i, g, h⟩ => ⟨B, i, e.comp g, h⟩, fun ⟨B, i, g, h⟩ => ⟨B, i, e.symm.comp g, h⟩⟩)

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

end Lax366625.CountingProblems
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

/-- Well-formedness: the order is linear, there is a position to start on, the
input is functional, and there is exactly one blank symbol. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

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

instance instIsRelationalTuring : IsRelational turing := fun _ => (inferInstance : IsEmpty Empty)

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

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

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

/-- The relational language of machines writing a number. -/
abbrev turingOut : Language.{0, 0} := turing.sum tapeOut

open FirstOrder

open Language Structure

namespace TMData

variable {A : Type} (M : TMData A)

end TMData

section Semantics

variable {A : Type} [turingOut.Structure A]

end Semantics

open Lax366625.CountingProblems

end Lax366625.MachineNumbers
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax366625.CountingRuns
section
namespace Lax366625.CountingRuns

open Lax366625.MachineNumbers Lax904597.Machines

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

namespace TMData

variable {A : Type} (M : TMData A)

/-- **A run laid out along the positions**: a configuration for each position,
initial at the lowest, related by a step – or by a stutter in an accepting
state, for a machine that has already accepted – at each immediate successor,
and accepting at the highest. -/
def IsWalk (conf : A → Config A) : Prop :=
  (∀ p, MinPos M.Le M.Posn p → M.IsInit (conf p)) ∧
    (∀ p q, SuccPos M.Le M.Posn p q →
      M.Step (conf p) (conf q) ∨ (M.Acc (conf p).state ∧ conf q = conf p)) ∧
    ∀ p, MaxPos M.Le M.Posn p → M.Acc (conf p).state

/-- **A halting walk**: a walk that repeats an accepting configuration once it
has reached one, and carries the initial configuration at the times that are
not positions. A run from an initial configuration to the first accepting one,
within the budget, has exactly one such layout. -/
def IsHaltWalk (conf : A → Config A) : Prop :=
  TMData.IsWalk M conf ∧
    (∀ p q, SuccPos M.Le M.Posn p q → M.Acc (conf p).state → conf q = conf p) ∧
    ∀ t p₀, ¬ M.Posn t → MinPos M.Le M.Posn p₀ → conf t = conf p₀

end TMData

open Lax366625.CountingProblems

/-- **Counting accepting runs**: the number of halting walks of the machine
described by the instance, an ill-formed instance having none. -/
noncomputable def SharpNTMAccept : CountingProblem turing :=
  CountingProblem.ofFun fun A _ => 
    Nat.card {conf : A → Config A // (tmData A).WellFormed ∧ TMData.IsHaltWalk (tmData A) conf}

end Lax366625.CountingRuns
end
