-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Graph
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax420092.QueryDatabases
section
namespace Lax420092.QueryDatabases

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryDbRel : ℕ → Type where
/-- `isVar x`: the element `x` is a variable of the query. -/
  | isVar : queryDbRel 1
/-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
  | atom : queryDbRel 2
/-- `fact a b`: the database contains the fact `E(a, b)`. -/
  | fact : queryDbRel 2
  deriving DecidableEq

/-- The relational language of BCQ evaluation instances: a query and a
database over a shared universe, with a unary predicate singling out the
query variables and binary predicates for query atoms and database facts. -/
def queryDb : FirstOrder.Language :=
  ⟨fun _ => Empty, queryDbRel⟩

instance instIsRelationalQueryDb : FirstOrder.Language.IsRelational queryDb := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `isVar x`: the element `x` is a variable of the query. -/
abbrev qdbIsVar : queryDb.Relations 1 :=
  .isVar

/-- `atom x y`: the query contains the atom `E(x, y)` (its arguments are
  variables or constants). -/
abbrev qdbAtom : queryDb.Relations 2 :=
  .atom

/-- `fact a b`: the database contains the fact `E(a, b)`. -/
abbrev qdbFact : queryDb.Relations 2 :=
  .fact

open FirstOrder

open Language Structure BoundedFormula

section EvalShorthands

variable {A : Type} [queryDb.Structure A]

/-- `x` is a variable of the query. -/
def QVar (x : A) : Prop := RelMap qdbIsVar ![x]

/-- `E(x, y)` is an atom of the query. -/
def QAtom (x y : A) : Prop := RelMap qdbAtom ![x, y]

/-- `E(a, b)` is a fact of the database (raw: no constraint on `a`, `b`). -/
def DbFact (x y : A) : Prop := RelMap qdbFact ![x, y]

/-- A genuine database edge: a fact both of whose endpoints are database
elements (i.e., not query variables). Facts violating this are representation
junk and are ignored by the semantics. -/
def DbEdge (x y : A) : Prop := DbFact x y ∧ ¬QVar x ∧ ¬QVar y

end EvalShorthands

end Lax420092.QueryDatabases
end

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

-- Lax420092.Evaluation
section
namespace Lax420092.Evaluation

open Lax420092.QueryDatabases

open FirstOrder

open Language Structure BoundedFormula

section GenericCore

variable {A B : Type}

/-- The conjunctive query with variables `VarP` and atoms `AtomP` (over
instance elements `A`) is satisfied in the database `F` on universe `U`,
where `ι` fixes the denotation of the non-variables: some valuation extends
`ι` and maps every atom to a database edge. -/
def SatisfiedIn (VarP : A → Prop) (AtomP : A → A → Prop) {U : Type}
    (F : U → U → Prop) (ι : A → U) : Prop :=
  ∃ v : A → U, (∀ x, ¬VarP x → v x = ι x) ∧ ∀ x y, AtomP x y → F (v x) (v y)

/-- The homomorphism condition: satisfaction in a database carried by the
instance's own universe, with every non-variable denoting itself. This single
notion underlies both problems below. -/
def CQHom (VarP : A → Prop) (AtomP FactP : A → A → Prop) : Prop :=
  SatisfiedIn VarP AtomP FactP id

end GenericCore

/-- The query of an evaluation instance holds in its database: there is a
valuation of the elements, fixing the non-variables, that maps every query
atom to a genuine database edge. This is the classical semantics of Boolean
conjunctive queries, phrased as a homomorphism into the database half of the
instance. -/
def QueryHolds (A : Type) [queryDb.Structure A] : Prop :=
  CQHom (QVar (A := A)) (QAtom (A := A)) (DbEdge (A := A))

open Lax904597.Problems Lax799700.Problems

/-- BCQ evaluation: does the query of the instance hold in its database? -/
def CQEval : DecisionProblem queryDb :=
  DecisionProblem.ofPred QueryHolds

end Lax420092.Evaluation
end
