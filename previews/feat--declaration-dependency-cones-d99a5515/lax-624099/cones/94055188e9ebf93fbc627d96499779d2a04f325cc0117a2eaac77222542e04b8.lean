-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
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
