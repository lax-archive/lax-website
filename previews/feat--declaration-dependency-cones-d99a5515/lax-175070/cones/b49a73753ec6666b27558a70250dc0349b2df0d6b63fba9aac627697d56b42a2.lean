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

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses
end Lax366625.CountingClasses

namespace Lax366625.CountingClasses.CountingClass
end Lax366625.CountingClasses.CountingClass
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

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax175070.CountDefinability
section
namespace Lax175070
end Lax175070

namespace Lax175070.CountDefinability
end Lax175070.CountDefinability
end

-- Lax904597.Sat
section
namespace Lax904597.Sat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

/-- The relation symbols of CNF instances. -/
inductive satRel : ℕ → Type where
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
def sat : Language :=
  ⟨fun _ => Empty, satRel⟩

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

end Lax904597.Sat
end

-- Lax366625.CountingSat
section
namespace Lax366625.CountingSat

open Lax904597.Sat

open FirstOrder

open Language Structure

section Sat

variable (A : Type) [sat.Structure A]

/-- The element `x` is a variable of the CNF formula: it occurs, positively or
negatively, in some clause. The decision problem does not need the notion –
an element in no clause is harmless – but everything that *counts* assignments
does, and so does any reduction that must not give such an element a truth
value to choose. -/
def SatOccurs (x : A) : Prop :=
  ∃ c : A, RelMap satIsClause ![c] ∧ (RelMap satPosIn ![c, x] ∨ RelMap satNegIn ![c, x])

end Sat

open FirstOrder

open Language Structure

section Models

variable (A : Type) [sat.Structure A]

/-- The set `ν` of true variables is a model of the CNF formula: every clause
contains a true literal, and `ν` consists of variables of the formula. -/
def SatModel (ν : A → Prop) : Prop :=
  (∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
  ∀ x : A, ν x → SatOccurs A x

end Models

open Lax366625.CountingProblems

end Lax366625.CountingSat
end

-- Lax175070.SelectedSat
section
namespace Lax175070.SelectedSat

open Lax366625.CountingSat Lax904597.Sat

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive selMarkRel : ℕ → Type where
/-- `sel x`: the variable `x` is selected. -/
  | sel : selMarkRel 1
  deriving DecidableEq

/-- The symbol selecting a variable. -/
def selMark : FirstOrder.Language :=
  ⟨fun _ => Empty, selMarkRel⟩

/-- `sel x`: the variable `x` is selected. -/
abbrev smSel : selMark.Relations 1 :=
  .sel

/-- The relational language of CNF formulas with a selected variable. -/
abbrev satSel : Language.{0, 0} := sat.sum selMark

open FirstOrder

open Language Structure

/-- “Is selected”, in the vocabulary of CNF formulas with a selected
variable. -/
abbrev ssSel : satSel.Relations 1 := Sum.inr smSel

/-- A CNF formula with a selected variable is a CNF formula. -/
instance satSelStructure (A : Type) [satSel.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satSel).reduct A

section Counts

variable (A : Type) [satSel.Structure A]

/-- A model of the formula in which every selected variable has the value
`b`. -/
def SelModel (b : Bool) (ν : A → Prop) : Prop :=
  SatModel A ν ∧ ∀ x : A, RelMap ssSel ![x] → (ν x ↔ b = true)

end Counts

open Lax904597.Problems Lax485149.Problems Lax366625.CountingProblems Lax175070.CountDefinability

end Lax175070.SelectedSat
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

-- Lax366625.MachineNumbers
section
namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax366625.MachineNumbers.TMData
end Lax366625.MachineNumbers.TMData

namespace Lax366625.MachineNumbers.tapeOutRel
end Lax366625.MachineNumbers.tapeOutRel

namespace Lax366625.MachineNumbers.tapeOutRel.one
end Lax366625.MachineNumbers.tapeOutRel.one

namespace Lax366625.MachineNumbers.tapeOutRel.out
end Lax366625.MachineNumbers.tapeOutRel.out
end

-- Lax366625.CountingRuns
section
namespace Lax366625.CountingRuns
end Lax366625.CountingRuns

namespace Lax366625.CountingRuns.TMData
end Lax366625.CountingRuns.TMData
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

-- Lax175070.CountingValues
section
namespace Lax175070.CountingValues

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems

open Lax485149.Complement

/-- The number of models with the selected variables at `b` is isomorphism-invariant. -/
axiom sharpSelSat_count_iso :
  ∀ (b : Bool) {A B : Type} [satSel.Structure A] [satSel.Structure B],
    (A ≃[satSel] B) → Nat.card {ν : A → Prop // SelModel A b ν} = Nat.card {ν : B → Prop //
        SelModel B b ν}

end Lax175070.CountingValues
end
