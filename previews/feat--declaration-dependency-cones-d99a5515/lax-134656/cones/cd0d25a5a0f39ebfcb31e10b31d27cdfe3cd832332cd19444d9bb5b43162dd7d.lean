-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
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

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992
end Lax535992

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
end Lax535992.InflationaryFixedPoint.StepDef
end

-- Lax134656.SecondOrderTransitiveClosure
section
namespace Lax134656
end Lax134656

namespace Lax134656.SecondOrderTransitiveClosure
end Lax134656.SecondOrderTransitiveClosure

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax134656.SecondOrderTransitiveClosure.SOTCSpec
end Lax134656.SecondOrderTransitiveClosure.SOTCSpec
end

-- Lax485149.Complement
section
namespace Lax485149
end Lax485149

namespace Lax485149.Complement
end Lax485149.Complement

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax134656.ClassPSPACE
section
namespace Lax134656.ClassPSPACE
end Lax134656.ClassPSPACE
end

-- Lax134656.OrderFreeTransitiveClosure
section
namespace Lax134656.OrderFreeTransitiveClosure
end Lax134656.OrderFreeTransitiveClosure

namespace Lax134656.OrderFreeTransitiveClosure.SOTCSpecFree
end Lax134656.OrderFreeTransitiveClosure.SOTCSpecFree
end

-- Lax134656.PartialFixedPoint
section
namespace Lax134656
end Lax134656

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef
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

-- Lax134656.Qsat
section
namespace Lax134656
end Lax134656

namespace Lax134656.Qsat
end Lax134656.Qsat

namespace Lax134656.Qsat.QsatWf
end Lax134656.Qsat.QsatWf

namespace Lax134656.Qsat.QsatWins
end Lax134656.Qsat.QsatWins

namespace Lax134656.Qsat.qsatRel
end Lax134656.Qsat.qsatRel

namespace Lax134656.Qsat.qsatRel.allVar
end Lax134656.Qsat.qsatRel.allVar

namespace Lax134656.Qsat.qsatRel.isClause
end Lax134656.Qsat.qsatRel.isClause

namespace Lax134656.Qsat.qsatRel.isVar
end Lax134656.Qsat.qsatRel.isVar

namespace Lax134656.Qsat.qsatRel.negIn
end Lax134656.Qsat.qsatRel.negIn

namespace Lax134656.Qsat.qsatRel.posIn
end Lax134656.Qsat.qsatRel.posIn

namespace Lax134656.Qsat.qsatRel.prefixLt
end Lax134656.Qsat.qsatRel.prefixLt
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
namespace Lax535992.DeterministicMachines

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Machines Lax485149.Problems

namespace TMData

variable {A : Type} (M : TMData A)

/-- **Determinism**: one start state, at most one transition applicable in a
given state on a given symbol, and at most one destination and written symbol
per transition. Together with well-formedness this leaves at most one step
from any configuration and at most one initial configuration, so the run is
unique. Every conjunct is first-order. -/
def Deterministic : Prop :=
  (∀ q q', M.Start q → M.Start q' → q = q') ∧
    (∀ τ τ' q a, M.Tr τ → M.Tr τ' → M.Src τ q → M.Src τ' q → M.Read τ a → M.Read τ' a →
      τ = τ') ∧
    (∀ τ q q', M.Dst τ q → M.Dst τ q' → q = q') ∧
    ∀ τ a a', M.Write τ a → M.Write τ a' → a = a'

end TMData

end Lax535992.DeterministicMachines
end

-- Lax134656.SpaceBoundedMachines
section
namespace Lax134656.SpaceBoundedMachines

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Machines Lax485149.Problems Lax535992.DeterministicMachines

namespace TMData

variable {A : Type} (M : TMData A)

/-- **Acceptance in bounded space**: some run from an initial configuration
reaches an accepting state, with *no bound on its length*. The space is
bounded by construction, the tape being indexed by the positions; a run may
visit exponentially many configurations, so acceptance is reachability in the
configuration graph. -/
def AcceptsSpace : Prop :=
  ∃ c₀ c : Config A, M.IsInit c₀ ∧ Relation.ReflTransGen M.Step c₀ c ∧ M.Acc c.state

end TMData

/-- The instance is a well-formed deterministic machine accepting in bounded
space. -/
def DTMAcceptsSpace (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.Deterministic (tmData A) ∧ TMData.AcceptsSpace (tmData A)

end Lax134656.SpaceBoundedMachines
end

-- Lax134656.SuccinctReach
section
namespace Lax134656
end Lax134656

namespace Lax134656.SuccinctReach
end Lax134656.SuccinctReach

namespace Lax134656.SuccinctReach.transSysRel
end Lax134656.SuccinctReach.transSysRel

namespace Lax134656.SuccinctReach.transSysRel.negIn
end Lax134656.SuccinctReach.transSysRel.negIn

namespace Lax134656.SuccinctReach.transSysRel.next
end Lax134656.SuccinctReach.transSysRel.next

namespace Lax134656.SuccinctReach.transSysRel.posIn
end Lax134656.SuccinctReach.transSysRel.posIn

namespace Lax134656.SuccinctReach.transSysRel.srcCl
end Lax134656.SuccinctReach.transSysRel.srcCl

namespace Lax134656.SuccinctReach.transSysRel.stateVar
end Lax134656.SuccinctReach.transSysRel.stateVar

namespace Lax134656.SuccinctReach.transSysRel.stepCl
end Lax134656.SuccinctReach.transSysRel.stepCl

namespace Lax134656.SuccinctReach.transSysRel.tgtCl
end Lax134656.SuccinctReach.transSysRel.tgtCl
end

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149
end Lax485149

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.SecondOrderAtoms.SOAtom
end Lax485149.SecondOrderAtoms.SOAtom
end

-- Lax535992.HornFragment
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornFragment.HornClause
end Lax535992.HornFragment.HornClause

namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram
end

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax564036.Hierarchy
section
namespace Lax564036
end Lax564036

namespace Lax564036.Hierarchy
end Lax564036.Hierarchy

namespace Lax564036.Hierarchy.SigmaP
end Lax564036.Hierarchy.SigmaP
end

-- Lax134656.SpaceBoundedMachineInvariance
section
namespace Lax134656.SpaceBoundedMachineInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Machines

open Lax485149.Problems Lax485149.Complement

open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME

open Lax564036.Hierarchy

open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure

open Lax134656.PartialFixedPoint

open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Being well-formed, deterministic and accepting in bounded space is
isomorphism-invariant. -/
axiom dtmAcceptsSpace_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → (DTMAcceptsSpace A ↔ DTMAcceptsSpace B)

end Lax134656.SpaceBoundedMachineInvariance
end
