-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
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

/-- A CNF instance is satisfiable if some assignment of truth values to its
elements makes every clause contain a true literal. -/
def Satisfiable (A : Type) [sat.Structure A] : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

end Lax904597.Sat
end

-- Lax535992.HornSat
section
namespace Lax535992.HornSat

open Lax904597.Problems Lax485149.Problems

open Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a CNF instance has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y

/-- A CNF instance is a yes-instance of HORN-SAT if every clause
has at most one positive literal and the CNF is satisfiable. -/
def HornSatisfiable : Prop :=
  AtMostOnePositive A ∧ Satisfiable A

end HornSat

end Lax535992.HornSat
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

-- Lax366625.HornNumbers
section
namespace Lax366625.HornNumbers

open Lax535992.HornSat Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section LeastModel

variable {A : Type} [sat.Structure A]

/-- The stages of unit propagation: `ForcedIn n x` says that `x` is the
positive literal of a clause whose negative literals are all forced in fewer
than `n` rounds. -/
def ForcedIn : ℕ → A → Prop
  | 0, _ => False
  | n + 1, x => ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → ForcedIn n y

/-- A variable is *forced* when some stage forces it. On a Horn formula this
is the least model of the implications. -/
def Forced (x : A) : Prop := ∃ n, ForcedIn n x

end LeastModel

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digitOrderRel : ℕ → Type where
/-- `out x`: the element `x` holds one digit. -/
  | out : digitOrderRel 1
/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  | below : digitOrderRel 2
  deriving DecidableEq

/-- The symbols reading a number off a set of marked elements. -/
def digitOrder : FirstOrder.Language :=
  ⟨fun _ => Empty, digitOrderRel⟩

/-- `out x`: the element `x` holds one digit. -/
abbrev dgoOut : digitOrder.Relations 1 :=
  .out

/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
abbrev dgoBelow : digitOrder.Relations 2 :=
  .below

/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := sat.sum digitOrder

open FirstOrder

open Language Structure

/-- “Is an output variable”. -/
abbrev hnOut : satOut.Relations 1 := Sum.inr dgoOut

/-- The comparison of the output variables. -/
abbrev hnBelow : satOut.Relations 2 := Sum.inr dgoBelow

/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [satOut.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satOut).reduct A

section Semantics

variable {A : Type} [satOut.Structure A]

/-- The output variable `x` is forced. -/
def ForcedDigit (x : A) : Prop :=
  RelMap hnOut ![x] ∧ Forced x

/-- `y` is an output variable strictly below `x`. -/
def LowerVar (x y : A) : Prop :=
  RelMap hnOut ![y] ∧ y ≠ x ∧ RelMap hnBelow ![y, x]

/-- The rank of a variable among the outputs: the number of output variables
strictly below it. -/
noncomputable def varRank (x : A) : ℕ :=
  Nat.card {y : A // LowerVar x y}

variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output variables. -/
def VarOrder : Prop :=
  (∀ p : A, RelMap hnOut ![p] → RelMap hnBelow ![p, p]) ∧
    (∀ p q r : A, RelMap hnOut ![p] → RelMap hnOut ![q] → RelMap hnOut ![r] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, r] → RelMap hnBelow ![p, r]) ∧
    (∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] ∨ RelMap hnBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by unit propagation**: each forced output variable
contributes two to the power of its rank among the outputs. Instances that are
not satisfiable Horn formulas, or whose outputs are not linearly ordered,
write `0`. -/
noncomputable def hornNumber : ℕ :=
  if HornSatisfiable A ∧ VarOrder A then ∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0
  else 0

end Semantics

open Lax366625.CountingProblems

end Lax366625.HornNumbers
end
