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

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

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
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

end Ordered

end Lax904597.Interpretations
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction

namespace Lax904597.Relativized

open FirstOrder FirstOrder.Language Lax904597.Problems Lax904597.Interpretations

/-- A relativized interpretation: an interpretation together with the domain
formula of each tag. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)

namespace RelFOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}

/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2

end RelFOInterpretation

end Lax904597.Relativized
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

/-- The relational vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

instance instIsRelationalLang (B : SOBlock) : IsRelational B.lang :=
  fun _ => ⟨fun f => Empty.elim f⟩

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

end Lax420092.Evaluation
end

-- Lax420092.PackagedInstances
section
namespace Lax420092.PackagedInstances.cqDecode
end Lax420092.PackagedInstances.cqDecode

namespace Lax420092.PackagedInstances.cqSize
end Lax420092.PackagedInstances.cqSize

namespace Lax420092.PackagedInstances.queryDbStructure
end Lax420092.PackagedInstances.queryDbStructure

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

/-- The `L`-structure a presentation presents. -/
instance FinPresentation.str {L : Language.{0, 0}} [L.IsRelational] (S : FinPresentation L) :
    L.Structure (Fin S.card) where
  funMap f := isEmptyElim f
  RelMap R x := S.relBool R x = true

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

/-- The structure a packaged instance encodes: variables and constants as
universe, the relations the encoder's computations read as propositions. -/
instance cqStructure (i : CQInstance) :
    queryDb.Structure (Fin i.vars ⊕ Fin (i.consts + 1)) where
  funMap f := isEmptyElim f
  RelMap R x := cqRelBool i R x = true

section Concrete

variable {V C : Type}

end Concrete

/-- Well-formedness of an evaluation instance: some element is a constant.
The one condition the decoder needs. -/
noncomputable def cqWFSentence : queryDb.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 1)
  (FirstOrder.Language.BoundedFormula.not
    (FirstOrder.Language.Relations.formula₁ qdbIsVar (FirstOrder.Language.Term.var (Sum.inr 0))))

section Decoder

variable (S : FinPresentation queryDb)

end Decoder

open Lax904597.Problems Lax799700.Problems Lax420092.Evaluation

/-- Evaluation on well-formed instances: those with at least one constant,
the ones the decoder handles. -/
def WFCQEval : DecisionProblem queryDb :=
  DecisionProblem.ofPred fun (A : Type) [queryDb.Structure A] =>
    A ⊨ cqWFSentence ∧ QueryHolds A

end Lax420092.PackagedInstances
end

-- Lax420092.QueryPairs
section
namespace Lax420092.QueryPairs

open Lax420092.Evaluation

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive queryPairRel : ℕ → Type where
/-- `leftVar x`: the element `x` is a variable of the left query. -/
  | leftVar : queryPairRel 1
/-- `rightVar x`: the element `x` is a variable of the right query. -/
  | rightVar : queryPairRel 1
/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
  | leftAtom : queryPairRel 2
/-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
  | rightAtom : queryPairRel 2
  deriving DecidableEq

/-- The relational language of pairs of conjunctive queries over a shared
universe of variables and constants. -/
def queryPair : FirstOrder.Language :=
  ⟨fun _ => Empty, queryPairRel⟩

instance instIsRelationalQueryPair : FirstOrder.Language.IsRelational queryPair := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure BoundedFormula

section PairShorthands

variable {A : Type} [queryPair.Structure A]

end PairShorthands

open Lax904597.Problems Lax799700.Problems

end Lax420092.QueryPairs
end

-- Lax420092.DecodingAndWellFormed
section
namespace Lax420092.DecodingAndWellFormed

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems

open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- The yes-instances of WFCQEval are exactly the structures with a constant
whose query holds. -/
axiom wfCQEval_iff : ∀ (A : Type) [queryDb.Structure A],
  WFCQEval A ↔ (A ⊨ cqWFSentence ∧ QueryHolds A)

end Lax420092.DecodingAndWellFormed
end
