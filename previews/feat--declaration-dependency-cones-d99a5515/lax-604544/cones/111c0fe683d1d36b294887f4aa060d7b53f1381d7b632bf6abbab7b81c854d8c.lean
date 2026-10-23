-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Basic
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

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
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

end Lax904597.SecondOrder
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

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

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

/-- An ordered first-order reduction from `P` to `Q`: an interpretation over
the ordered expansion of `L` that maps yes-instances of `P` exactly to
yes-instances of `Q`, on every finite nonempty structure and for every linear
order on it. -/
structure OrderedFOReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags: the copies of `A^dim` the interpretation uses. -/
  Tag : Type
  /-- Finitely many tags, so that finite structures map to finite ones. -/
  [tagFinite : Finite Tag]
  /-- At least one tag, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the interpretation. -/
  dim : ℕ
  /-- The interpretation, over the ordered expansion of `L`. -/
  toInterpretation : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

end Lax904597.Interpretations
end

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.KromFragment.KromClause
end Lax485149.KromFragment.KromClause

namespace Lax485149.KromFragment.KromLit
end Lax485149.KromFragment.KromLit

namespace Lax485149.KromFragment.KromProgram
end Lax485149.KromFragment.KromProgram
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

end Lax904597.Classes
end

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL
end Lax485149.ClassNL
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

instance instIsRelationalSat : IsRelational sat := fun _ => (inferInstance : IsEmpty Empty)

end Lax904597.Sat
end

-- Lax485149.TwoSat
section
namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc
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

-- Lax535992.HornSat
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornSat
end Lax535992.HornSat
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

-- Lax564036.Tautology
section
namespace Lax564036
end Lax564036

namespace Lax564036.Tautology
end Lax564036.Tautology
end

-- Lax604544.RelationIsomorphism
section
namespace Lax604544
end Lax604544

namespace Lax604544.RelationIsomorphism
end Lax604544.RelationIsomorphism
end

-- Lax604544.DagIsomorphism
section
namespace Lax604544.DagIsomorphism

open Lax904597.Problems Lax485149.Problems Lax604544.RelationIsomorphism

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoDagsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern DAG. -/
  | patV : twoDagsRel 1
/-- `hostV a`: `a` is a vertex of the host DAG. -/
  | hostV : twoDagsRel 1
/-- `patArc a b`: there is an arc of the pattern DAG from `a` to `b`. -/
  | patArc : twoDagsRel 2
/-- `hostArc a b`: there is an arc of the host DAG from `a` to `b`. -/
  | hostArc : twoDagsRel 2
/-- `patLt a b`: `a` precedes `b` in the pattern's topological order. -/
  | patLt : twoDagsRel 2
/-- `hostLt a b`: `a` precedes `b` in the host's topological order. -/
  | hostLt : twoDagsRel 2
  deriving DecidableEq

/-- The relational language of two directed acyclic graphs: two arc relations
sharing a universe, each with its own vertex mark and its own topological
order. -/
def twoDags : FirstOrder.Language :=
  ⟨fun _ => Empty, twoDagsRel⟩

instance instIsRelationalTwoDags : FirstOrder.Language.IsRelational twoDags := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Topo

variable {A : Type}

end Topo

section Shorthands

variable {A : Type} [twoDags.Structure A]

end Shorthands

section Problem

variable (A : Type) [twoDags.Structure A]

end Problem

end Lax604544.DagIsomorphism
end

-- Lax604544.Degrees
section
namespace Lax604544.Degrees

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Classes

/-- **The degree of a problem**: the problems that ordered first-order reduce
to `Q₀`, as a complexity class with cofinal hardness. -/
def below {L₀ : Language.{0, 0}} [L₀.IsRelational] (Q₀ : DecisionProblem L₀) : ComplexityClass :=
  ComplexityClass.ofMem fun P => Nonempty (OrderedFOReduction P Q₀)

end Lax604544.Degrees
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

-- Lax799700.SubgraphIso
section
namespace Lax799700.SubgraphIso

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoGraphsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern graph. -/
  | patV : twoGraphsRel 1
/-- `hostV a`: `a` is a vertex of the host graph. -/
  | hostV : twoGraphsRel 1
/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
  | patE : twoGraphsRel 2
/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
  | hostE : twoGraphsRel 2
  deriving DecidableEq

/-- The relational language of pattern-and-host graphs: two graphs sharing a
universe, each with its own vertex mark and adjacency relation. -/
def twoGraphs : FirstOrder.Language :=
  ⟨fun _ => Empty, twoGraphsRel⟩

instance instIsRelationalTwoGraphs : FirstOrder.Language.IsRelational twoGraphs := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

end Generic

section Problem

section Shorthands

variable {A : Type} [twoGraphs.Structure A]

end Shorthands

variable (A : Type) [twoGraphs.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SubgraphIso
end

-- Lax604544.GraphIsomorphism
section
namespace Lax604544.GraphIsomorphism
end Lax604544.GraphIsomorphism
end

-- Lax624099.ValueInvention
section
namespace Lax624099.ValueInvention

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language marking the original elements inside an
extended universe. -/
inductive oldRel : ℕ → Type
  /-- `old x`: the element `x` comes from the original structure, i.e., it is
  not an invented value. -/
  | old : oldRel 1
  deriving DecidableEq

/-- The one-symbol relational language marking, inside a universe extended
with invented values, the elements of the original structure. -/
def oldMark : Language :=
  ⟨fun _ => Empty, oldRel⟩

instance instIsRelationalOldMark : IsRelational oldMark :=
  fun _ => ⟨fun f => Empty.elim f⟩

open FirstOrder

open Language Structure

/-- The vocabulary of extended structures: the base vocabulary together with
the unary predicate `old` marking the elements of the original structure. -/
abbrev newLang (L : Language.{0, 0}) : Language := L.sum oldMark

section Extended

/-- The original elements of a universe extended by invented values. The
invented values are an arbitrary type, so that the same predicate reads an
extension by a *set* of them and not only by an initial segment. -/
def IsOld {A N : Type} : A ⊕ N → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The base structure carried by the extended universe: a relation symbol
holds of a tuple exactly when all its entries are original elements and it
holds of them in `A`. Invented values are related to nothing. -/
@[reducible]
def extBase (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ) :
    L.Structure (A ⊕ Fin m) where
  funMap f := isEmptyElim f
  RelMap {_k} r x := ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y

/-- The interpretation of the marking predicate on the extended universe. -/
@[reducible]
def oldMarkStructure (A : Type) (m : ℕ) : oldMark.Structure (A ⊕ Fin m) where
  RelMap | .old => fun x => IsOld (x 0)

/-- **The extended structure**: the instance `A` together with `m` invented
values, over the vocabulary `DescriptiveComplexity.newLang L`. -/
instance extStructure (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A]
    (m : ℕ) : (newLang L).Structure (A ⊕ Fin m) :=
  @sumStructure L oldMark (A ⊕ Fin m) (extBase L A m) (oldMarkStructure A m)

end Extended

section Definability

variable {L : Language.{0, 0}}

/-- **Definability in `∃SO[new]`**, existential second-order logic with value
invention: on nonempty finite structures, `P A` holds exactly when, for *some*
number `m` of invented values, the relation variables of the block `B` can be
assigned relations over the extended universe `A ⊕ Fin m` satisfying the
first-order kernel `φ` in the extended structure.

The number `m` of invented values is unbounded, which is precisely what takes
the notion beyond `Σ₁` (`DescriptiveComplexity.SigmaSODefinable`, where the
certificate lives over `A` itself): a witness is a finite object, but no
function of `|A|` bounds its size. -/
def SigmaSONewDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ B : SOBlock, ∃ φ : (soLang (newLang L) [B]).Sentence,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true

end Definability

end Lax624099.ValueInvention
end

-- Lax624099.ClassRE
section
namespace Lax624099.ClassRE.DecisionProblem
end Lax624099.ClassRE.DecisionProblem

namespace Lax624099.ClassRE

open Lax904597.Problems Lax904597.Classes Lax624099.ValueInvention

open FirstOrder

open Language

/-- **RE**, the recursively enumerable problems: the class of the
`∃SO[new]`-definable problems, with cofinal hardness. -/
noncomputable def RE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSONewDefinable P

end Lax624099.ClassRE
end

-- Lax624099.Problems
section
namespace Lax624099.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax624099.Problems
end

-- Lax624099.FiniteSatisfiability
section
namespace Lax624099.FiniteSatisfiability

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of encoded first-order sentences in
negation normal form. -/
inductive finsatRel : ℕ → Type
  /-- `le x y`: the order of the syntax. -/
  | le : finsatRel 2
  /-- `andN g`: the node `g` is the conjunction of its children. -/
  | andN : finsatRel 1
  /-- `orN g`: the node `g` is the disjunction of its children. -/
  | orN : finsatRel 1
  /-- `allN g`: the node `g` universally quantifies its bound variable. -/
  | allN : finsatRel 1
  /-- `exN g`: the node `g` existentially quantifies its bound variable. -/
  | exN : finsatRel 1
  /-- `child g c`: the node `c` is one of the children of the node `g`. -/
  | child : finsatRel 2
  /-- `bind g x`: the quantifier node `g` binds the variable `x`. -/
  | bind : finsatRel 2
  /-- `eqL g x y`: the node `g` is the literal `x = y`. -/
  | eqL : finsatRel 3
  /-- `neqL g x y`: the node `g` is the literal `x ≠ y`. -/
  | neqL : finsatRel 3
  /-- `posL g s`: the node `g` is a positive atom of the relation symbol
  `s`. -/
  | posL : finsatRel 2
  /-- `negL g s`: the node `g` is a negated atom of the relation symbol
  `s`. -/
  | negL : finsatRel 2
  /-- `arg g p x`: the argument of the atom `g` at position `p` is the
  variable `x`. -/
  | arg : finsatRel 3
  /-- `sig s p`: the relation symbol `s` has an argument position `p`. -/
  | sig : finsatRel 2
  /-- `root g`: the node `g` is the root of the encoded sentence. -/
  | root : finsatRel 1
  deriving DecidableEq

/-- The relational vocabulary of encoded first-order sentences: a parse DAG in
negation normal form, ordered by the order of its own syntax. -/
def finsat : Language :=
  ⟨fun _ => Empty, finsatRel⟩

instance instIsRelationalFinsat : IsRelational finsat :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The order symbol of the syntax. -/
abbrev finsatLeSym : finsat.Relations 2 := .le

/-- The symbol marking conjunction nodes. -/
abbrev finsatAndSym : finsat.Relations 1 := .andN

/-- The symbol marking disjunction nodes. -/
abbrev finsatOrSym : finsat.Relations 1 := .orN

/-- The symbol marking universal quantifier nodes. -/
abbrev finsatAllSym : finsat.Relations 1 := .allN

/-- The symbol marking existential quantifier nodes. -/
abbrev finsatExSym : finsat.Relations 1 := .exN

/-- The symbol of the child relation of the parse DAG. -/
abbrev finsatChildSym : finsat.Relations 2 := .child

/-- The symbol binding a variable to a quantifier node. -/
abbrev finsatBindSym : finsat.Relations 2 := .bind

/-- The symbol of positive equality literals. -/
abbrev finsatEqSym : finsat.Relations 3 := .eqL

/-- The symbol of negated equality literals. -/
abbrev finsatNeqSym : finsat.Relations 3 := .neqL

/-- The symbol of positive atoms. -/
abbrev finsatPosSym : finsat.Relations 2 := .posL

/-- The symbol of negated atoms. -/
abbrev finsatNegSym : finsat.Relations 2 := .negL

/-- The symbol giving the arguments of an atom. -/
abbrev finsatArgSym : finsat.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev finsatSigSym : finsat.Relations 2 := .sig

/-- The symbol marking the root node. -/
abbrev finsatRootSym : finsat.Relations 1 := .root

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

/-- `x` precedes `y` in the order of the syntax. -/
def Ord (x y : A) : Prop := RelMap finsatLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the syntax. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The node `g` is a conjunction. -/
def AndG (g : A) : Prop := RelMap finsatAndSym ![g]

/-- The node `g` is a disjunction. -/
def OrG (g : A) : Prop := RelMap finsatOrSym ![g]

/-- The node `g` is a universal quantifier. -/
def AllG (g : A) : Prop := RelMap finsatAllSym ![g]

/-- The node `g` is an existential quantifier. -/
def ExG (g : A) : Prop := RelMap finsatExSym ![g]

/-- The node `c` is a child of the node `g`. -/
def ChildG (g c : A) : Prop := RelMap finsatChildSym ![g, c]

/-- The quantifier node `g` binds the variable `x`. -/
def BindG (g x : A) : Prop := RelMap finsatBindSym ![g, x]

/-- The node `g` is the literal `x = y`. -/
def EqG (g x y : A) : Prop := RelMap finsatEqSym ![g, x, y]

/-- The node `g` is the literal `x ≠ y`. -/
def NeqG (g x y : A) : Prop := RelMap finsatNeqSym ![g, x, y]

/-- The node `g` is a positive atom of the symbol `s`. -/
def PosG (g s : A) : Prop := RelMap finsatPosSym ![g, s]

/-- The node `g` is a negated atom of the symbol `s`. -/
def NegG (g s : A) : Prop := RelMap finsatNegSym ![g, s]

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
def ArgG (g p x : A) : Prop := RelMap finsatArgSym ![g, p, x]

/-- The symbol `s` has an argument position `p`. -/
def SigG (s p : A) : Prop := RelMap finsatSigSym ![s, p]

/-- The node `g` is the root of the encoded sentence. -/
def RootG (g : A) : Prop := RelMap finsatRootSym ![g]

end Reading

/-- **Well-formedness of an encoded sentence**: the order symbol is a linear
order and the parse DAG descends along it. -/
structure IsWF (A : Type) [finsat.Structure A] : Prop where
  /-- The order of the syntax is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the syntax is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the syntax is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the syntax is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- Children come strictly earlier: the parse DAG is acyclic. -/
  child_lt : ∀ g c : A, ChildG g c → OrdLt c g
  /-- An atom has at most one argument at each position. -/
  arg_fun : ∀ g p x x' : A, ArgG g p x → ArgG g p x' → x = x'
  /-- An atom has at most one relation symbol. -/
  atom_sym : ∀ g s s' : A, (PosG g s ∨ NegG g s) → (PosG g s' ∨ NegG g s') → s = s'
  /-- An atom only has arguments at the positions of its symbol's signature. -/
  arg_sig : ∀ g s p x : A, (PosG g s ∨ NegG g s) → ArgG g p x → SigG s p
  /-- An atom has an argument at every position of its symbol's signature. -/
  arg_tot : ∀ g s p : A, (PosG g s ∨ NegG g s) → SigG s p → ∃ x, ArgG g p x

open Classical in
/-- Updating an environment at one variable. (Classical: the instance is a
bare type, with no decidable equality.) -/
noncomputable def upd {A M : Type} (v : A → M) (x : A) (d : M) : A → M :=
  fun z => if z = x then d else v z

section Semantics

variable {A M : Type} [finsat.Structure A]

/-- **One unfolding of the truth definition**: the value of the node `g` under
the environment `v`, given the values `rec` of the nodes below it. A
conjunction node holds when all its children do, a disjunction node when one
of them does, a quantifier node when all (respectively one) of the values of
its bound variable make all (one of) its children hold; a literal reads the
environment, an atom the interpretation `I`, on an assignment `w` of the
argument positions matching the environment on the arguments of the atom. -/
noncomputable def gstep (I : A → (A → M) → Prop) (rec : (A → M) → A → Prop)
    (v : A → M) (g : A) : Prop :=
  (AndG g ∧ ∀ c, ChildG g c → rec v c) ∨
  (OrG g ∧ ∃ c, ChildG g c ∧ rec v c) ∨
  (AllG g ∧ ∀ x, BindG g x → ∀ d : M, ∀ c, ChildG g c → rec (upd v x d) c) ∨
  (ExG g ∧ ∃ x, BindG g x ∧ ∃ d : M, ∃ c, ChildG g c ∧ rec (upd v x d) c) ∨
  (∃ x y, EqG g x y ∧ v x = v y) ∨
  (∃ x y, NeqG g x y ∧ v x ≠ v y) ∨
  (∃ s, PosG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ I s w) ∨
  (∃ s, NegG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ ¬I s w)

/-- **Satisfaction, by iteration**: `gval I k v g` is the `k`-th approximant of
the truth of the node `g` under the environment `v`. -/
noncomputable def gval (I : A → (A → M) → Prop) : ℕ → (A → M) → A → Prop
  | 0 => fun _ _ => False
  | k + 1 => gstep I (gval I k)

/-- **The node `g` holds under the environment `v`**: the least fixed point of
the truth definition, reached because a finite parse DAG has finite depth. -/
def Gval (I : A → (A → M) → Prop) (v : A → M) (g : A) : Prop :=
  ∃ k, gval I k v g

/-- An interpretation is **local** when the value of a symbol depends only on
the arguments its signature declares. -/
def Local (I : A → (A → M) → Prop) : Prop :=
  ∀ (s : A) (w w' : A → M), (∀ p, SigG s p → w p = w' p) → (I s w ↔ I s w')

end Semantics

/-- **The encoded sentence has a finite model**: the instance is well-formed
and there is a finite nonempty universe with a local interpretation of the
relation symbols under which every environment satisfies the root – that is, a
finite model of the universal closure of the encoded formula. -/
def FinSatOn (A : Type) [finsat.Structure A] : Prop :=
  IsWF A ∧ ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : A → (A → M) → Prop),
    Local I ∧ ∀ (v : A → M) (g : A), RootG g → Gval I v g

end FinSat

open Lax904597.Problems Lax624099.Problems

/-- FINSAT: does the encoded first-order sentence have a finite model? -/
def FINSAT : DecisionProblem finsat :=
  DecisionProblem.ofPred FinSat.FinSatOn

end Lax624099.FiniteSatisfiability
end

-- Lax604544.ClassesAsDegrees
section
namespace Lax604544.ClassesAsDegrees

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Sat Lax799700.SubgraphIso

open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME

open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability

open Lax604544.Degrees Lax604544.RelationIsomorphism

open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- RE is the degree of FINSAT. -/
axiom RE_eq_below_finsat : RE = below FINSAT

end Lax604544.ClassesAsDegrees
end
