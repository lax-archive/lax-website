-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
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

-- Lax859101.CountingAllSets
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingAllSets
end Lax859101.CountingAllSets
end

-- Lax859101.CountingBipartite
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingBipartite
end Lax859101.CountingBipartite

namespace Lax859101.CountingBipartite.bipGraphRel
end Lax859101.CountingBipartite.bipGraphRel

namespace Lax859101.CountingBipartite.bipGraphRel.edge
end Lax859101.CountingBipartite.bipGraphRel.edge

namespace Lax859101.CountingBipartite.bipGraphRel.left
end Lax859101.CountingBipartite.bipGraphRel.left
end

-- Lax859101.CountingDnf
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingDnf
end Lax859101.CountingDnf
end

-- Lax799700.NaeSat
section
namespace Lax799700.NaeSat
end Lax799700.NaeSat
end

-- Lax859101.CountingNaeSat
section
namespace Lax859101
end Lax859101

namespace Lax859101.CountingNaeSat
end Lax859101.CountingNaeSat
end

-- Lax799700.Common
section
namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc
end

-- Lax859101.CountingRestrictedSat
section
namespace Lax859101.CountingRestrictedSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y

end HornSat

open FirstOrder

open Language Structure

section TwoSat

variable (A : Type) [sat.Structure A]

end TwoSat

open FirstOrder

open Language Structure

section Sentences

variable {α : Type}

variable {A : Type} [sat.Structure A]

end Sentences

open Lax366625.CountingProblems Lax366625.CountingSat

end Lax859101.CountingRestrictedSat
end

-- Lax859101.OneCallReductions
section
namespace Lax859101
end Lax859101

namespace Lax859101.OneCallReductions
end Lax859101.OneCallReductions

namespace Lax859101.OneCallReductions.OneCallReduction
end Lax859101.OneCallReductions.OneCallReduction

namespace Lax859101.OneCallReductions.PolyTerm
end Lax859101.OneCallReductions.PolyTerm

namespace Lax859101.OneCallReductions.PostTerm
end Lax859101.OneCallReductions.PostTerm

namespace Lax859101.OneCallReductions.PolyTerm.add
end Lax859101.OneCallReductions.PolyTerm.add

namespace Lax859101.OneCallReductions.PolyTerm.card
end Lax859101.OneCallReductions.PolyTerm.card

namespace Lax859101.OneCallReductions.PolyTerm.eval
end Lax859101.OneCallReductions.PolyTerm.eval

namespace Lax859101.OneCallReductions.PolyTerm.mul
end Lax859101.OneCallReductions.PolyTerm.mul

namespace Lax859101.OneCallReductions.PolyTerm.num
end Lax859101.OneCallReductions.PolyTerm.num

namespace Lax859101.OneCallReductions.PostTerm.add
end Lax859101.OneCallReductions.PostTerm.add

namespace Lax859101.OneCallReductions.PostTerm.div
end Lax859101.OneCallReductions.PostTerm.div

namespace Lax859101.OneCallReductions.PostTerm.eval
end Lax859101.OneCallReductions.PostTerm.eval

namespace Lax859101.OneCallReductions.PostTerm.mod
end Lax859101.OneCallReductions.PostTerm.mod

namespace Lax859101.OneCallReductions.PostTerm.mul
end Lax859101.OneCallReductions.PostTerm.mul

namespace Lax859101.OneCallReductions.PostTerm.oracle
end Lax859101.OneCallReductions.PostTerm.oracle

namespace Lax859101.OneCallReductions.PostTerm.poly
end Lax859101.OneCallReductions.PostTerm.poly

namespace Lax859101.OneCallReductions.PostTerm.pow2
end Lax859101.OneCallReductions.PostTerm.pow2

namespace Lax859101.OneCallReductions.PostTerm.sub
end Lax859101.OneCallReductions.PostTerm.sub
end

-- Lax859101.SubtractiveReductions
section
namespace Lax859101
end Lax859101

namespace Lax859101.SubtractiveReductions
end Lax859101.SubtractiveReductions

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax859101.SubtractiveReductions.StrongSubtractiveReduction
end Lax859101.SubtractiveReductions.StrongSubtractiveReduction

namespace Lax859101.SubtractiveReductions.SubtractiveReducible
end Lax859101.SubtractiveReductions.SubtractiveReducible

namespace Lax859101.SubtractiveReductions.FOInterpretation.ordExtend
end Lax859101.SubtractiveReductions.FOInterpretation.ordExtend
end

-- Lax859101.RestrictedSatValues
section
namespace Lax859101.RestrictedSatValues

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax904597.Sat Lax799700.SetFamily

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat

open Lax859101.OneCallReductions Lax859101.SubtractiveReductions Lax859101.CountingDnf
    Lax859101.CountingNaeSat Lax859101.CountingRestrictedSat Lax859101.CountingAllSets
        Lax859101.CountingBipartite

/-- The number counted by #HORN-SAT is isomorphism-invariant. -/
axiom sharpHornSat_count_iso :
  ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
    (A ≃[Lax904597.Sat.sat] B) → Nat.card
        {ν : A → Prop // AtMostOnePositive A ∧ SatModel A ν} = Nat.card
            {ν : B → Prop // AtMostOnePositive B ∧ SatModel B ν}

end Lax859101.RestrictedSatValues
end
