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

-- Lax134656.SuccinctReach
section
namespace Lax134656.SuccinctReach

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive transSysRel : ℕ → Type where
/-- `stateVar x`: the element `x` is a state variable. -/
  | stateVar : transSysRel 1
/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
  | next : transSysRel 2
/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
  | stepCl : transSysRel 1
/-- `srcCl c`: the element `c` is a clause of the source formula. -/
  | srcCl : transSysRel 1
/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
  | tgtCl : transSysRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : transSysRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : transSysRel 2
  deriving DecidableEq

/-- The relational vocabulary of succinctly described transition systems: the
state variables and their next-state copies, three groups of clauses, and the
two literal-occurrence predicates of CNF instances. -/
def transSys : FirstOrder.Language :=
  ⟨fun _ => Empty, transSysRel⟩

/-- `stateVar x`: the element `x` is a state variable. -/
abbrev tsStateVar : transSys.Relations 1 :=
  .stateVar

/-- `next x y`: the element `y` is the next-state copy of the state
  variable `x`. -/
abbrev tsNext : transSys.Relations 2 :=
  .next

/-- `stepCl c`: the element `c` is a clause of the transition formula. -/
abbrev tsStepCl : transSys.Relations 1 :=
  .stepCl

/-- `srcCl c`: the element `c` is a clause of the source formula. -/
abbrev tsSrcCl : transSys.Relations 1 :=
  .srcCl

/-- `tgtCl c`: the element `c` is a clause of the target formula. -/
abbrev tsTgtCl : transSys.Relations 1 :=
  .tgtCl

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev tsPosIn : transSys.Relations 2 :=
  .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev tsNegIn : transSys.Relations 2 :=
  .negIn

open FirstOrder

open Language Structure

section Semantics

variable (A : Type) [transSys.Structure A]

/-- A valuation satisfies a group of clauses when every clause of the group
contains a literal it makes true. Elements that are not clauses of the group
impose nothing, exactly as for satisfiability. -/
def ClausesHold (ν : A → Prop) (grp : transSys.Relations 1) : Prop :=
  ∀ c : A, RelMap grp ![c] →
    ∃ x : A, (RelMap tsPosIn ![c, x] ∧ ν x) ∨ (RelMap tsNegIn ![c, x] ∧ ¬ν x)

/-- The valuation `ν` *reads* the state `S`: on every state variable it agrees
with `S`. This is the only way a clause group sees the current state. -/
def ReadsCur (ν : A → Prop) (S : A → Prop) : Prop :=
  ∀ x : A, RelMap tsStateVar ![x] → (ν x ↔ S x)

/-- The valuation `ν` *writes* the state `S'`: on the next-state copy of every
state variable it holds exactly the value `S'` gives to that variable. -/
def WritesNext (ν : A → Prop) (S' : A → Prop) : Prop :=
  ∀ x y : A, RelMap tsStateVar ![x] → RelMap tsNext ![x, y] → (ν y ↔ S' x)

/-- One transition of the system: some valuation satisfies every transition
clause while reading `S` on the state variables and writing `S'` on their
next-state copies. The valuation is existentially quantified, so the auxiliary
variables of the transition formula are free to take whatever values the
clauses need. -/
def StepRel (S S' : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsStepCl ∧ ReadsCur A ν S ∧ WritesNext A ν S'

/-- A state is a source state when some valuation reading it satisfies every
clause of the source formula. -/
def IsStart (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsSrcCl ∧ ReadsCur A ν S

/-- A state is a target state when some valuation reading it satisfies every
clause of the target formula. -/
def IsGoal (S : A → Prop) : Prop :=
  ∃ ν : A → Prop, ClausesHold A ν tsTgtCl ∧ ReadsCur A ν S

/-- **The yes-instances of SUCCINCT-REACH**: some target state is reachable
from some source state along the transitions described by the clauses. -/
def SuccinctReachable : Prop :=
  ∃ S S' : A → Prop, IsStart A S ∧ IsGoal A S' ∧ Relation.ReflTransGen (StepRel A) S S'

end Semantics

end Lax134656.SuccinctReach
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

-- Lax134656.SuccinctReachInvariance
section
namespace Lax134656.SuccinctReachInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Machines

open Lax485149.Problems Lax485149.Complement

open Lax535992.InflationaryFixedPoint Lax535992.DeterministicMachines Lax535992.ClassPTIME

open Lax564036.Hierarchy

open Lax134656.SecondOrderTransitiveClosure Lax134656.OrderFreeTransitiveClosure

open Lax134656.PartialFixedPoint

open Lax134656.Qsat Lax134656.SuccinctReach Lax134656.SpaceBoundedMachines Lax134656.ClassPSPACE

/-- Succinct reachability is isomorphism-invariant. -/
axiom succinctReachable_iso : ∀ {A B : Type} [transSys.Structure A] [transSys.Structure B],
  (A ≃[transSys] B) → (SuccinctReachable A ↔ SuccinctReachable B)

end Lax134656.SuccinctReachInvariance
end
