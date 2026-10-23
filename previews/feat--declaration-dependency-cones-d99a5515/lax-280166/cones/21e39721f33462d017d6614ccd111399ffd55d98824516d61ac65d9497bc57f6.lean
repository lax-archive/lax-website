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
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Set
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

-- Lax799700.Problems
section
namespace Lax799700
end Lax799700

namespace Lax799700.Problems
end Lax799700.Problems

namespace Lax799700.Problems.DecisionProblem
end Lax799700.Problems.DecisionProblem

namespace Lax799700.Problems.DecisionProblem.ofPred
end Lax799700.Problems.DecisionProblem.ofPred
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax799700.CliqueFamily
section
namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.CliqueFamily.markedGraphRel
end Lax799700.CliqueFamily.markedGraphRel

namespace Lax799700.CliqueFamily.markedGraphRel.adj
end Lax799700.CliqueFamily.markedGraphRel.adj

namespace Lax799700.CliqueFamily.markedGraphRel.marked
end Lax799700.CliqueFamily.markedGraphRel.marked
end

-- Lax280166.CountingCliques
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingCliques
end Lax280166.CountingCliques
end

-- Lax280166.CountingDominatingSets
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingDominatingSets
end Lax280166.CountingDominatingSets
end

-- Lax799700.Feedback
section
namespace Lax799700.Feedback
end Lax799700.Feedback

namespace Lax799700.Feedback.markedArcGraphRel
end Lax799700.Feedback.markedArcGraphRel

namespace Lax799700.Feedback.markedArcGraphRel.adj
end Lax799700.Feedback.markedArcGraphRel.adj

namespace Lax799700.Feedback.markedArcGraphRel.marked
end Lax799700.Feedback.markedArcGraphRel.marked
end

-- Lax280166.CountingFeedbackSets
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingFeedbackSets
end Lax280166.CountingFeedbackSets
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

-- Lax799700.Hamilton
section
namespace Lax799700.Hamilton
end Lax799700.Hamilton

namespace Lax799700.Hamilton.digraphRel
end Lax799700.Hamilton.digraphRel

namespace Lax799700.Hamilton.digraphRel.arc
end Lax799700.Hamilton.digraphRel.arc
end

-- Lax280166.CountingHamiltonCircuits
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingHamiltonCircuits
end Lax280166.CountingHamiltonCircuits
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

-- Lax799700.Common
section
namespace Lax799700.Common

open Lax904597.Sat

section Decode

variable {A : Type}

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses, so that stray
`posIn`/`negIn` facts on non-clause elements do not create gadgets. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

/-- The literal `(x, s)` is true under the assignment `ν`. -/
def LitTrue (ν : A → Prop) (x : A) (s : Bool) : Prop := if s then ν x else ¬ν x

end SatOcc

end Lax799700.Common
end

-- Lax799700.Knapsack
section
namespace Lax799700.Knapsack
end Lax799700.Knapsack

namespace Lax799700.Knapsack.binWeightsRel
end Lax799700.Knapsack.binWeightsRel

namespace Lax799700.Knapsack.binWeightsRel.bit
end Lax799700.Knapsack.binWeightsRel.bit

namespace Lax799700.Knapsack.binWeightsRel.item
end Lax799700.Knapsack.binWeightsRel.item

namespace Lax799700.Knapsack.binWeightsRel.le
end Lax799700.Knapsack.binWeightsRel.le

namespace Lax799700.Knapsack.binWeightsRel.posn
end Lax799700.Knapsack.binWeightsRel.posn

namespace Lax799700.Knapsack.binWeightsRel.tgt
end Lax799700.Knapsack.binWeightsRel.tgt
end

-- Lax799700.ZeroOneIP
section
namespace Lax799700.ZeroOneIP
end Lax799700.ZeroOneIP

namespace Lax799700.ZeroOneIP.zeroOneIPRel
end Lax799700.ZeroOneIP.zeroOneIPRel

namespace Lax799700.ZeroOneIP.zeroOneIPRel.coef
end Lax799700.ZeroOneIP.zeroOneIPRel.coef

namespace Lax799700.ZeroOneIP.zeroOneIPRel.col
end Lax799700.ZeroOneIP.zeroOneIPRel.col

namespace Lax799700.ZeroOneIP.zeroOneIPRel.le
end Lax799700.ZeroOneIP.zeroOneIPRel.le

namespace Lax799700.ZeroOneIP.zeroOneIPRel.posn
end Lax799700.ZeroOneIP.zeroOneIPRel.posn

namespace Lax799700.ZeroOneIP.zeroOneIPRel.rhs
end Lax799700.ZeroOneIP.zeroOneIPRel.rhs

namespace Lax799700.ZeroOneIP.zeroOneIPRel.row
end Lax799700.ZeroOneIP.zeroOneIPRel.row
end

-- Lax280166.CountingKnapsacks
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingKnapsacks
end Lax280166.CountingKnapsacks
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

end Models

open Lax366625.CountingProblems

end Lax366625.CountingSat
end

-- Lax799700.OneInSat
section
namespace Lax799700.OneInSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Semantics

variable {A : Type} [sat.Structure A]

/-- An assignment is *exactly-one proper* when every clause has exactly one
true literal occurrence. -/
def OneInProper (ν : A → Prop) : Prop :=
  ∀ c : A, SatOcc.IsCl c → ∃ x s, SatOcc.OccIn c x s ∧ SatOcc.LitTrue ν x s ∧
    ∀ y t, SatOcc.OccIn c y t → SatOcc.LitTrue ν y t → y = x ∧ t = s

end Semantics

section Problem

variable (A : Type) [sat.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.OneInSat
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat
end Lax799700.ThreeSat
end

-- Lax280166.CountingSatVariants
section
namespace Lax280166.CountingSatVariants

open Lax366625.CountingSat Lax799700.OneInSat Lax904597.Sat

open FirstOrder

open Language Structure

/-- The set `ν` of true variables is an exactly-one model of the CNF formula:
every clause has exactly one true literal, and `ν` consists of variables of
the formula. -/
def OneInModel (A : Type) [sat.Structure A] (ν : A → Prop) : Prop :=
  OneInProper ν ∧ ∀ x : A, ν x → SatOccurs A x

open Lax366625.CountingProblems Lax366625.CountingSat Lax799700.ThreeSat

end Lax280166.CountingSatVariants
end

-- Lax799700.SetFamily
section
namespace Lax799700.SetFamily
end Lax799700.SetFamily

namespace Lax799700.SetFamily.setSystemRel
end Lax799700.SetFamily.setSystemRel

namespace Lax799700.SetFamily.setSystemRel.elem
end Lax799700.SetFamily.setSystemRel.elem

namespace Lax799700.SetFamily.setSystemRel.fam
end Lax799700.SetFamily.setSystemRel.fam

namespace Lax799700.SetFamily.setSystemRel.marked
end Lax799700.SetFamily.setSystemRel.marked

namespace Lax799700.SetFamily.setSystemRel.mem
end Lax799700.SetFamily.setSystemRel.mem
end

-- Lax280166.CountingSetFamilies
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingSetFamilies
end Lax280166.CountingSetFamilies
end

-- Lax799700.Steiner
section
namespace Lax799700.Steiner
end Lax799700.Steiner

namespace Lax799700.Steiner.steinerGraphRel
end Lax799700.Steiner.steinerGraphRel

namespace Lax799700.Steiner.steinerGraphRel.adj
end Lax799700.Steiner.steinerGraphRel.adj

namespace Lax799700.Steiner.steinerGraphRel.marked
end Lax799700.Steiner.steinerGraphRel.marked

namespace Lax799700.Steiner.steinerGraphRel.terminal
end Lax799700.Steiner.steinerGraphRel.terminal
end

-- Lax280166.CountingSteinerTrees
section
namespace Lax280166
end Lax280166

namespace Lax280166.CountingSteinerTrees
end Lax280166.CountingSteinerTrees
end

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses
end Lax366625.CountingClasses

namespace Lax366625.CountingClasses.CountingClass
end Lax366625.CountingClasses.CountingClass
end

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
end

-- Lax799700.DominatingSet
section
namespace Lax799700.DominatingSet
end Lax799700.DominatingSet
end

-- Lax280166.SatVariantsValues
section
namespace Lax280166.SatVariantsValues

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Sat

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax799700.ThreeSat Lax799700.SetFamily

open Lax280166.CountingSatVariants Lax280166.CountingCliques Lax280166.CountingDominatingSets
    Lax280166.CountingFeedbackSets Lax280166.CountingHamiltonCircuits Lax280166.CountingSetFamilies
        Lax280166.CountingKnapsacks Lax280166.CountingSteinerTrees

/-- The number counted by #1-in-SAT is isomorphism-invariant. -/
axiom sharpOneInSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card {ν : A → Prop // OneInModel A ν} = Nat.card {ν : B → Prop
        // OneInModel B ν}

end Lax280166.SatVariantsValues
end
