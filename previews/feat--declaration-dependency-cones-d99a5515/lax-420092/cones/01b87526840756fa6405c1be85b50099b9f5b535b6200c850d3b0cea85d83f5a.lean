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

/-- A relativized ordered first-order reduction from `P` to `Q`. -/
structure RelOrderedFOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited: some tagged tuple satisfies its tag's
  domain formula. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toRelInterpretation.MapRel A)

end Lax904597.Relativized
end

-- Lax904597.SecondOrder
section
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

/-- An assignment of actual relations on a universe `A` to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

/-- The structure over the block's vocabulary determined by an assignment. -/
@[reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

/-- The base vocabulary expanded by the vocabularies of a list of blocks. -/
def soLang (L : Language.{0, 0}) : List SOBlock → Language.{0, 0}
  | [] => L
  | B :: Bs => soLang (L.sum B.lang) Bs

/-- Alternating second-order satisfaction: the sentence obtained from the
first-order kernel `φ` by quantifying the blocks `Bs` alternately,
existentially first when `pol` is `true`, holds in the `L`-structure `A`. -/
def SORealize (L : Language.{0, 0}) (A : Type) [inst : L.Structure A] :
    ∀ (Bs : List SOBlock), (soLang L Bs).Sentence → Bool → Prop
  | [], φ, _ => @Sentence.Realize L A inst φ
  | B :: Bs, φ, true =>
      ∃ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ false
  | B :: Bs, φ, false =>
      ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ))
          Bs φ true

variable {L : Language.{0, 0}}

/-- A decision problem is `Σₖ`-definable if, on nonempty finite structures, it
is defined by a second-order sentence with `k` alternating blocks of
second-order quantifiers, starting existentially. -/
def SigmaSODefinable [L.IsRelational] (k : ℕ) (P : DecisionProblem L) : Prop :=
  ∃ Bs : List SOBlock, Bs.length = k ∧
    ∃ φ : (soLang L Bs).Sentence,
      ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A], P A ↔ SORealize L A Bs φ true

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

/-- A complexity class: a membership predicate and a hardness predicate on
decision problems, over arbitrary relational vocabularies. -/
structure ComplexityClass where
  /-- The problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to. -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Cofinal hardness for a collection of problems: every problem of the
collection reduces to every relational problem that `P` reduces to. -/
def CofinalHard (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (RelOrderedFOReduction P S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (RelOrderedFOReduction Q S)

/-- The class with the given membership and cofinal hardness. -/
def ComplexityClass.ofMem
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop) :
    ComplexityClass where
  Mem P := Mem P
  Hard P := CofinalHard Mem P

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def ComplexityClass.Complete (C : ComplexityClass) (P : DecisionProblem L) : Prop :=
  C.Mem P ∧ C.Hard P

/-- The level `Σₖ₊₁ᵖ` of the polynomial hierarchy: the problems definable with
`k + 1` alternating blocks of second-order quantifiers, existential first. -/
def sigmaLevel (k : ℕ) : ComplexityClass :=
  .ofMem fun P => SigmaSODefinable (k + 1) P

/-- NP is `Σ₁ᵖ`: by definition, the existential-second-order definable
problems (Fagin's theorem). -/
def NP : ComplexityClass := sigmaLevel 0

end Lax904597.Classes
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

end GenericCore

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

section Decoder

variable (S : FinPresentation queryDb)

end Decoder

open Lax904597.Problems Lax799700.Problems Lax420092.Evaluation

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

/-- `leftVar x`: the element `x` is a variable of the left query. -/
abbrev qpLeftVar : queryPair.Relations 1 :=
  .leftVar

/-- `rightVar x`: the element `x` is a variable of the right query. -/
abbrev qpRightVar : queryPair.Relations 1 :=
  .rightVar

/-- `leftAtom x y`: the left query contains the atom `E(x, y)`. -/
abbrev qpLeftAtom : queryPair.Relations 2 :=
  .leftAtom

/-- `rightAtom x y`: the right query contains the atom `E(x, y)`. -/
abbrev qpRightAtom : queryPair.Relations 2 :=
  .rightAtom

open FirstOrder

open Language Structure BoundedFormula

section PairShorthands

variable {A : Type} [queryPair.Structure A]

/-- `x` is a variable of the left query. -/
def LVar (x : A) : Prop := RelMap qpLeftVar ![x]

/-- `x` is a variable of the right query. -/
def RVar (x : A) : Prop := RelMap qpRightVar ![x]

/-- `E(x, y)` is an atom of the left query. -/
def LAtom (x y : A) : Prop := RelMap qpLeftAtom ![x, y]

/-- `E(x, y)` is an atom of the right query. -/
def RAtom (x y : A) : Prop := RelMap qpRightAtom ![x, y]

/-- `x` is a variable of either query; the non-`PairVar` elements are the
shared constants, whose denotation every database fixes. -/
def PairVar (x : A) : Prop := LVar x ∨ RVar x

end PairShorthands

/-- The left query is contained in the right one: every database (over any
universe, with any interpretation of the constants) satisfying the left query
satisfies the right query. -/
def QueryContained (A : Type) [queryPair.Structure A] : Prop :=
  ∀ (U : Type) (F : U → U → Prop) (ι : A → U),
    SatisfiedIn (PairVar (A := A)) (LAtom (A := A)) F ι →
      SatisfiedIn (PairVar (A := A)) (RAtom (A := A)) F ι

open Lax904597.Problems Lax799700.Problems

/-- BCQ containment: is the left query contained in the right one? -/
def CQContainment : DecisionProblem queryPair :=
  DecisionProblem.ofPred QueryContained

end Lax420092.QueryPairs
end

-- Lax420092.ContainmentNPComplete
section
namespace Lax420092.ContainmentNPComplete

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes Lax799700.Problems

open Lax420092.QueryDatabases Lax420092.Evaluation Lax420092.QueryPairs Lax420092.PackagedInstances

/-- CQContainment is NP-complete. -/
axiom cqContainment_NP_complete : NP.Complete CQContainment

end Lax420092.ContainmentNPComplete
end
