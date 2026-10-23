-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

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

-- Lax624099.ClassRE
section
namespace Lax624099.ClassRE

open Lax904597.Problems Lax904597.Classes Lax624099.ValueInvention

open FirstOrder

open Language

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

/-- **co-RE**: the problems whose complement is recursively enumerable. -/
noncomputable def coRE : ComplexityClass :=
  ComplexityClass.ofMem fun P => SigmaSONewDefinable (DecisionProblem.compl P)

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

-- Lax624099.CodeHalting
section
namespace Lax624099.CodeHalting

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of code instances. -/
inductive codeRel : ℕ → Type
  /-- `croot n`: `n` is the root of the syntax tree. -/
  | croot : codeRel 1
  /-- `czero n`: `n` draws the constructor `zero`. -/
  | czero : codeRel 1
  /-- `csucc n`: `n` draws the constructor `succ`. -/
  | csucc : codeRel 1
  /-- `cleft n`: `n` draws the constructor `left`. -/
  | cleft : codeRel 1
  /-- `cright n`: `n` draws the constructor `right`. -/
  | cright : codeRel 1
  /-- `cpair n`: `n` draws the constructor `pair`. -/
  | cpair : codeRel 1
  /-- `ccomp n`: `n` draws the constructor `comp`. -/
  | ccomp : codeRel 1
  /-- `cprec n`: `n` draws the constructor `prec`. -/
  | cprec : codeRel 1
  /-- `crfind n`: `n` draws the constructor `rfind'`. -/
  | crfind : codeRel 1
  /-- `carg1 n m`: `m` is the first child of `n`. -/
  | carg1 : codeRel 2
  /-- `carg2 n m`: `m` is the second child of `n`. -/
  | carg2 : codeRel 2
  deriving DecidableEq

/-- The relational language of code instances: the eight constructor marks,
the mark of the root, and the two child relations. -/
def code : Language :=
  ⟨fun _ => Empty, codeRel⟩

instance instIsRelationalCode : IsRelational code :=
  fun _ => ⟨fun f => Empty.elim f⟩

/-- The root symbol. -/
abbrev cRoot : code.Relations 1 := .croot

/-- The `zero` symbol. -/
abbrev cZero : code.Relations 1 := .czero

/-- The `succ` symbol. -/
abbrev cSucc : code.Relations 1 := .csucc

/-- The `left` symbol. -/
abbrev cLeft : code.Relations 1 := .cleft

/-- The `right` symbol. -/
abbrev cRight : code.Relations 1 := .cright

/-- The `pair` symbol. -/
abbrev cPair : code.Relations 1 := .cpair

/-- The `comp` symbol. -/
abbrev cComp : code.Relations 1 := .ccomp

/-- The `prec` symbol. -/
abbrev cPrec : code.Relations 1 := .cprec

/-- The `rfind'` symbol. -/
abbrev cRfind : code.Relations 1 := .crfind

/-- The first-child symbol. -/
abbrev cArg1 : code.Relations 2 := .carg1

/-- The second-child symbol. -/
abbrev cArg2 : code.Relations 2 := .carg2

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [code.Structure A]

/-- Being the root. -/
def CRoot (a : A) : Prop := RelMap cRoot ![a]

/-- Drawing the constructor `zero`. -/
def CZero (a : A) : Prop := RelMap cZero ![a]

/-- Drawing the constructor `succ`. -/
def CSucc (a : A) : Prop := RelMap cSucc ![a]

/-- Drawing the constructor `left`. -/
def CLeft (a : A) : Prop := RelMap cLeft ![a]

/-- Drawing the constructor `right`. -/
def CRight (a : A) : Prop := RelMap cRight ![a]

/-- Drawing the constructor `pair`. -/
def CPair (a : A) : Prop := RelMap cPair ![a]

/-- Drawing the constructor `comp`. -/
def CComp (a : A) : Prop := RelMap cComp ![a]

/-- Drawing the constructor `prec`. -/
def CPrec (a : A) : Prop := RelMap cPrec ![a]

/-- Drawing the constructor `rfind'`. -/
def CRfind (a : A) : Prop := RelMap cRfind ![a]

/-- Being the first child. -/
def CArg1 (a b : A) : Prop := RelMap cArg1 ![a, b]

/-- Being the second child. -/
def CArg2 (a b : A) : Prop := RelMap cArg2 ![a, b]

end Shorthands

section Decode

variable {A : Type} [code.Structure A]

/-- **The node `n` draws the code `c`.** A recursion on the code: the mark of
the node must be the constructor's, and its children must draw the
constructor's arguments. -/
def DecodesTo (n : A) : Nat.Partrec.Code → Prop
  | .zero => CZero n
  | .succ => CSucc n
  | .left => CLeft n
  | .right => CRight n
  | .pair cf cg =>
      CPair n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .comp cf cg =>
      CComp n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .prec cf cg =>
      CPrec n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .rfind' cf => CRfind n ∧ ∃ a, CArg1 n a ∧ DecodesTo a cf

end Decode

open Lax904597.Problems Lax624099.Problems

/-- The root of the instance draws a code halting on `0`. -/
def CodeHaltsOn (A : Type) [code.Structure A] : Prop :=
  ∃ (n : A) (c : Nat.Partrec.Code), CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom

/-- CODEHALT: does the partial recursive code drawn in the instance halt on
`0`? -/
def CODEHALT : DecisionProblem code :=
  DecisionProblem.ofPred CodeHaltsOn

end Lax624099.CodeHalting
end

-- Lax624099.FiniteSatisfiability
section
namespace Lax624099.FiniteSatisfiability.FinSat.IsWF
end Lax624099.FiniteSatisfiability.FinSat.IsWF

namespace Lax624099.FiniteSatisfiability.FinSat.gval
end Lax624099.FiniteSatisfiability.FinSat.gval

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

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

end Reading

section Semantics

variable {A M : Type} [finsat.Structure A]

end Semantics

end FinSat

open Lax904597.Problems Lax624099.Problems

end Lax624099.FiniteSatisfiability
end

-- Lax904597.Machines
section
namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

instance instIsRelationalTuring : IsRelational turing := fun _ => (inferInstance : IsEmpty Empty)

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
end

-- Lax624099.ConcreteInstances
section
namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax624099.ConcreteInstances

open Lax904597.Problems

open FirstOrder

open FirstOrder.Language Structure

section Digits

/-- The number of a tuple of digits, little-endian in base `c`. -/
def tupleIdx (c : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + c * tupleIdx c l

end Digits

/-- A **finitely presented relational vocabulary**: the relation symbols of `L`
numbered by `Fin numSyms`, with their arities. Reading a symbol off its number
(`sym`) and numbering a symbol (`index`) are mutually inverse, so the
presentation loses nothing.

Every vocabulary of the catalog is of this shape: `Language.turing` has 12
symbols of arity at most 2, `Language.finsat` 14 of arity at most 3. The
presentations are closed under `Language.sum`
(`FirstOrder.Language.FinVocab.sum`), which is what lets the second-order
machinery – whose vocabularies are sums of the instance's with a block's – be
encoded by the same means. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The number of relation symbols. -/
  numSyms : ℕ
  /-- The symbol with a given number, together with its arity. -/
  symOf : Fin numSyms → ((n : ℕ) × L.Relations n)
  /-- The number of a symbol. -/
  index : ∀ {n : ℕ}, L.Relations n → Fin numSyms
  /-- Reading back the symbol with the number of a symbol gives it back. -/
  symOf_index : ∀ {n : ℕ} (R : L.Relations n), symOf (index R) = ⟨n, R⟩
  /-- Numbering the symbol with a given number gives that number back. -/
  index_symOf : ∀ i : Fin numSyms, index (symOf i).2 = i

namespace FinVocab

variable {L : Language.{0, 0}} (V : FinVocab L)

end FinVocab

/-- A **concrete finite structure** over the finitely presented vocabulary
`V`: a universe size and a table of Booleans, one row per relation symbol.

The universe is `Fin (univSize + 1)`, so it is nonempty by construction; the
row of an `n`-ary symbol is read at the number of the tuple, little-endian in
base `card`. Anything out of range reads `false`, so every pair of a number
and a list of lists of Booleans denotes a structure. -/
structure FinStruct {L : Language.{0, 0}} (V : FinVocab L) where
  /-- One less than the size of the universe. -/
  univSize : ℕ
  /-- The tables of the relations, one row per symbol. -/
  table : List (List Bool)

namespace FinStruct

variable {L : Language.{0, 0}} {V : FinVocab L}

/-- The size of the universe of a concrete finite structure. -/
abbrev card (s : FinStruct V) : ℕ := s.univSize + 1

/-- The universe of a concrete finite structure: nonempty and linearly ordered
by construction. -/
abbrev Univ (s : FinStruct V) : Type := Fin s.card

/-- The table lookup: does the relation `R` hold of the tuple `x`? -/
def relMapBool (s : FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) : Bool :=
  (s.table.getD (V.index R) []).getD (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false

/-- **The structure a piece of data denotes.** -/
instance instStructure [L.IsRelational] (s : FinStruct V) : L.Structure s.Univ where
  funMap f := isEmptyElim f
  RelMap R x := s.relMapBool R x = true

/-- The coding of a concrete finite structure as a pair. -/
def equivProd (V : FinVocab L) : FinStruct V ≃ ℕ × List (List Bool) where
  toFun s := (s.univSize, s.table)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- **Concrete finite structures are a `Primcodable` type**: the object
`ComputablePred` and `REPred` are defined on. -/
instance instPrimcodable (V : FinVocab L) : Primcodable (FinStruct V) :=
  Primcodable.ofEquiv _ (equivProd V)

end FinStruct

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

open FirstOrder

open FirstOrder.Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

end FinVocab

open Lax904597.Machines Lax624099.FiniteSatisfiability Lax624099.CodeHalting

instance instDecidableEqSigmaNatRelationsTuring : DecidableEq ((n : ℕ) × turing.Relations n) := by
  show DecidableEq ((n : ℕ) × turingRel n)
  infer_instance

instance instDecidableEqSigmaNatRelationsFinsat : DecidableEq ((n : ℕ) × finsat.Relations n) := by
  show DecidableEq ((n : ℕ) × finsatRel n)
  infer_instance

instance instDecidableEqSigmaNatRelationsCode : DecidableEq ((n : ℕ) × code.Relations n) := by
  show DecidableEq ((n : ℕ) × codeRel n)
  infer_instance

end Lax624099.ConcreteInstances
end

-- Lax624099.Halting
section
namespace Lax624099.Halting
end Lax624099.Halting

namespace Lax624099.Halting.ConfigU
end Lax624099.Halting.ConfigU

namespace Lax624099.Halting.TMData
end Lax624099.Halting.TMData

namespace Lax624099.Halting.ConfigU.ext
end Lax624099.Halting.ConfigU.ext

namespace Lax624099.Halting.TMData.StepsInU
end Lax624099.Halting.TMData.StepsInU
end

-- Lax624099.PostCorrespondence
section
namespace Lax624099.PostCorrespondence.Pcp.IsWF
end Lax624099.PostCorrespondence.Pcp.IsWF

namespace Lax624099.PostCorrespondence

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of Post correspondence systems. -/
inductive pcpRel : ℕ → Type
  /-- `le x y`: the order of the positions. -/
  | le : pcpRel 2
  /-- `dom d`: the element `d` is one of the dominoes. -/
  | dom : pcpRel 1
  /-- `uAt d p c`: the top word of the domino `d` has the letter `c` at the
  position `p`. -/
  | uAt : pcpRel 3
  /-- `vAt d p c`: the bottom word of the domino `d` has the letter `c` at the
  position `p`. -/
  | vAt : pcpRel 3
  deriving DecidableEq

/-- The relational vocabulary of Post correspondence systems: marked dominoes
carrying two words each, over a universe ordered by the order of the positions
of those words. -/
def pcp : Language :=
  ⟨fun _ => Empty, pcpRel⟩

instance instIsRelationalPcp : IsRelational pcp :=
  fun _ => ⟨fun f => Empty.elim f⟩

open FirstOrder

open Language Structure

namespace Pcp

section Reading

variable {A : Type} [pcp.Structure A]

end Reading

section Words

variable {A : Type} [pcp.Structure A]

end Words

end Pcp

open Lax904597.Problems Lax624099.Problems

end Lax624099.PostCorrespondence
end

-- Lax624099.RENeCoRE
section
namespace Lax624099.RENeCoRE

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE

open Lax624099.FiniteSatisfiability

open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence

open Lax624099.ConcreteInstances

/-- CODEHALT is not in co-RE. -/
axiom codehalt_not_mem_coRE : ¬coRE.Mem CODEHALT

end Lax624099.RENeCoRE
end
