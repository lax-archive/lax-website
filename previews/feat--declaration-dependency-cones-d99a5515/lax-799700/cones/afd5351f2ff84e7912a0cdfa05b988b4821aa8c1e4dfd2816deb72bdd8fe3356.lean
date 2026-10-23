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
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax799700.Problems
section
namespace Lax799700.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax799700.Problems
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

instance instIsRelationalSat : IsRelational sat := fun _ => (inferInstance : IsEmpty Empty)

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

/-- A `Language.sat`-structure is exactly-one satisfiable if some assignment
gives every clause exactly one true literal. -/
def OneInSatisfiable : Prop := ∃ ν : A → Prop, OneInProper ν

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem OneInSAT: does the structure satisfy `OneInSatisfiable`? -/
def OneInSAT : DecisionProblem Lax904597.Sat.sat :=
  DecisionProblem.ofPred OneInSatisfiable

end Lax799700.OneInSat
end
