-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax799700.NaeSat
section
namespace Lax799700.NaeSat

open Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock BoundedFormula

section Semantics

variable {A : Type} [sat.Structure A]

/-- An assignment is *not-all-equal proper* when every clause contains both a
true and a false literal. -/
def NAEProper (ν : A → Prop) : Prop :=
  ∀ c : A, RelMap satIsClause ![c] →
    (∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)) ∧
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ¬ν x) ∨ (RelMap satNegIn ![c, x] ∧ ν x)

end Semantics

section Problem

variable (A : Type) [sat.Structure A]

/-- A `Language.sat`-structure is not-all-equal satisfiable if some assignment
gives every clause both a true and a false literal. -/
def NAESatisfiable : Prop := ∃ ν : A → Prop, NAEProper ν

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.NaeSat
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

end SatOcc

end Lax799700.Common
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section ThreeSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most three literal
occurrences: among any four occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostThree : Prop :=
  ∀ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

end ThreeSat

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.ThreeSat
end

-- Lax799700.NaeThreeSat
section
namespace Lax799700.NaeThreeSat

open Lax799700.NaeSat Lax799700.ThreeSat Lax904597.Sat

open FirstOrder

open Language Structure

section Problem

variable (A : Type) [sat.Structure A]

/-- A `Language.sat`-structure is a yes-instance of NAE-3SAT if every clause
has at most three literal occurrences and some assignment gives every clause
both a true and a false literal. -/
def NAEThreeSatisfiable : Prop :=
  WidthAtMostThree A ∧ NAESatisfiable A

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The property `NAEThreeSatisfiable` is isomorphism-invariant. -/
axiom naeThreeSatisfiable_iso : ∀ {A B : Type} [Lax904597.Sat.sat.Structure A] [Lax904597.Sat.sat.Structure B],
  (A ≃[Lax904597.Sat.sat] B) → (NAEThreeSatisfiable A ↔ NAEThreeSatisfiable B)

end Lax799700.NaeThreeSat
end
