-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Sort
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

open FirstOrder

open Language Structure BoundedFormula

section EvalShorthands

variable {A : Type} [queryDb.Structure A]

end EvalShorthands

end Lax420092.QueryDatabases
end

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

-- Lax420092.Evaluation
section
namespace Lax420092.Evaluation
end Lax420092.Evaluation
end

-- Lax420092.PackagedInstances
section
namespace Lax420092.PackagedInstances.cqDecode
end Lax420092.PackagedInstances.cqDecode

namespace Lax420092.PackagedInstances.cqSize
end Lax420092.PackagedInstances.cqSize

namespace Lax420092.PackagedInstances

open Lax420092.QueryDatabases

open FirstOrder

open Language Structure

/-- A concretely presented finite `L`-structure: a size and a computable
relation table. This is the input type of decoders – the “raw bytes” a
decoding computation reads. -/
structure FinPresentation (L : Language.{0, 0}) where
  /-- The number of elements. -/
  card : ℕ
  /-- The relations, as computations on `Fin card`. -/
  relBool : ∀ {n}, L.Relations n → (Fin n → Fin card) → Bool

section Concrete

variable {V C : Type}

end Concrete

/-- A packaged concrete evaluation instance: `n` query variables, `m + 1`
database constants, a finite set of query atoms over them, and a finite set
of database facts on the constants. -/
structure CQInstance where
  /-- The number of query variables. -/
  vars : ℕ
  /-- The number of constants, minus one: constants are `Fin (consts + 1)`,
  so the database domain is never empty. -/
  consts : ℕ
  /-- The query atoms, over variables and constants. -/
  atoms : Finset ((Fin vars ⊕ Fin (consts + 1)) × (Fin vars ⊕ Fin (consts + 1)))
  /-- The database facts, over the constants. -/
  facts : Finset (Fin (consts + 1) × Fin (consts + 1))
  deriving DecidableEq

open FirstOrder

open Language Structure BoundedFormula

/-- The encoder itself, standalone rather than inline in the bundle, so that
it can be audited in isolation: it elaborates as a plain `def` – an encoder
deciding an undecidable predicate could not, the compiler would demand
`noncomputable` – and it genuinely runs (the `#guard`s below). Its
`#print axioms` still cites the classical axioms, harmlessly: `Finset`
membership is decided through `Multiset` quotients, whose instances cite them
in *proof* positions only – executability is witnessed by execution, not by
the axiom report. -/
def cqRelBool (i : CQInstance) {n : ℕ} (R : queryDb.Relations n) :
    (Fin n → (Fin i.vars ⊕ Fin (i.consts + 1))) → Bool :=
  match n, R with
  | _, .isVar => fun x => (x 0).isLeft
  | _, .atom => fun x => decide ((x 0, x 1) ∈ i.atoms)
  | _, .fact => fun x =>
    match x 0, x 1 with
    | Sum.inr a, Sum.inr b => decide ((a, b) ∈ i.facts)
    | _, _ => false

section Concrete

variable {V C : Type}

/-- The `Language.queryDb`-structure encoding a concrete instance: universe
`V ⊕ C`, the variables being the left summands, with the atoms of `q` and
the facts of `D`. -/
@[reducible]
def queryDbStructure (q : List ((V ⊕ C) × (V ⊕ C))) (D : List (C × C)) :
    queryDb.Structure (V ⊕ C) where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .isVar => fun x =>
      match x 0 with
      | Sum.inl _ => True
      | Sum.inr _ => False
    | _, .atom => fun x => (x 0, x 1) ∈ q
    | _, .fact => fun x =>
      match x 0, x 1 with
      | Sum.inr a, Sum.inr b => (a, b) ∈ D
      | _, _ => False

end Concrete

section Decoder

variable (S : FinPresentation queryDb)

end Decoder

open Lax904597.Problems Lax799700.Problems Lax420092.Evaluation

end Lax420092.PackagedInstances
end
