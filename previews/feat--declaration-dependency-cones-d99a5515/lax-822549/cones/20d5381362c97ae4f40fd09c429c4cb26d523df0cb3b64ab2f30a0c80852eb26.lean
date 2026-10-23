-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
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

-- Lax485149.Problems
section
namespace Lax485149.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax485149.Problems
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

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

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

-- Lax535992.DeterministicMachines
section
namespace Lax535992
end Lax535992

namespace Lax535992.DeterministicMachines
end Lax535992.DeterministicMachines

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData
end

-- Lax134656.SpaceBoundedMachines
section
namespace Lax134656
end Lax134656

namespace Lax134656.SpaceBoundedMachines
end Lax134656.SpaceBoundedMachines

namespace Lax134656.SpaceBoundedMachines.TMData
end Lax134656.SpaceBoundedMachines.TMData
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

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax480241.Expansions
section
namespace Lax480241.Expansions

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

namespace SOBlock

/-- `n` independent copies of a block: one relation variable per pair of a copy
index and a relation variable of `B`, keeping its arity. -/
def replicate (B : SOBlock) (n : ℕ) : SOBlock where
  ι := Fin n × B.ι
  arity p := B.arity p.2

/-- The assignment of the replicated block determined by one assignment per
copy. The index type being a plain product, this is currying and nothing
more. -/
def replicateAssign (B : SOBlock) {A : Type} {n : ℕ} (ρs : Fin n → B.Assignment A) :
    (SOBlock.replicate B n).Assignment A :=
  fun p => ρs p.1 p.2

end SOBlock

instance instFiniteAssignment {B : SOBlock} {A : Type} [Finite A] : Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))

variable {L : Language.{0, 0}}

section Expand

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[reducible]
def SOBlock.structure₁ (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

end Expand

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- An **exponential expansion** of `L`-structures into `E`-structures: the
universe is a definable set of tagged assignments of the block `B`, and each
relation symbol of `E` is defined, at each tuple of tags, by a first-order
sentence over the ordered base vocabulary expanded by one copy of the block per
argument. -/
structure ExpExpansion (L : Language.{0, 0}) : Type 1 where
  /-- The tags: finitely many copies of the space of block assignments. -/
  Tag : Type
  /-- Tags are finite, so that finite structures expand to finite
  structures. -/
  [tagFinite : Finite Tag]
  /-- The block whose assignments are the points of the expanded universe. -/
  B : SOBlock
  /-- The vocabulary of the expanded structure. -/
  E : Language.{0, 0}
  /-- The expanded vocabulary is relational, as every vocabulary of this
  library. -/
  [eRelational : E.IsRelational]
  /-- The domain sentence of each tag: a tagged assignment `(t, ρ)` is a point
  of the expanded universe iff `dom t` holds of `ρ`. -/
  dom : Tag → ((L.sum Language.order).sum B.lang).Sentence
  /-- The defining sentence of each relation symbol at each tuple of tags, over
  as many copies of the block as the symbol has arguments. -/
  relSentence : ∀ {n : ℕ}, E.Relations n → (Fin n → Tag) →
    ((L.sum Language.order).sum (SOBlock.replicate B n).lang).Sentence
  /-- The definable domain is inhabited, so that nonempty structures expand to
  nonempty structures. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (ρ : B.Assignment A),
      @Sentence.Realize _ A (SOBlock.structure₁ B (L := L.sum Language.order) ρ) (dom t)

namespace ExpExpansion

variable (X : ExpExpansion L)

attribute [instance] tagFinite eRelational

/-- A candidate point of the expanded universe: a tagged assignment of the
block. An `abbrev`, so that the pair structure stays visible to `rw` and to
instance search – only `ExpExpansion.Map` needs to be
opaque, to carry the expanded structure. -/
abbrev Point (A : Type) : Type :=
  X.Tag × X.B.Assignment A

variable {X}

/-- The domain condition on a candidate point: its tag's domain sentence holds
of its assignment. -/
def DomHolds {A : Type} [L.Structure A] [LinearOrder A] (p : X.Point A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ X.B (L := L.sum Language.order) p.2) (X.dom p.1)

variable (X)

/-- **The expanded universe**: the tagged block assignments satisfying their
tag's domain sentence. -/
def Map (A : Type) [L.Structure A] [LinearOrder A] : Type :=
  {p : X.Point A // DomHolds p}

variable {X}

/-- The point of the expanded universe carried by a tag and an assignment
satisfying the domain sentence. -/
def pt {A : Type} [L.Structure A] [LinearOrder A] (t : X.Tag) (ρ : X.B.Assignment A)
    (h : DomHolds (X := X) (t, ρ)) : X.Map A :=
  ⟨(t, ρ), h⟩

variable (X)

/-- **The expanded structure**: an `n`-ary symbol holds of `n` points iff its
defining sentence, at their tags, holds in the base structure with the `n`
copies of the block interpreted by their assignments. -/
instance mapStructure (A : Type) [L.Structure A] [LinearOrder A] :
    X.E.Structure (X.Map A) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    @Sentence.Realize _ A
      (SOBlock.structure₁ (SOBlock.replicate X.B n) (L := L.sum Language.order)
        (SOBlock.replicateAssign X.B fun i => (xs i).1.2))
      (X.relSentence r fun i => (xs i).1.1)

instance mapFinite (A : Type) [L.Structure A] [LinearOrder A] [Finite A] :
    Finite (X.Map A) :=
  inferInstanceAs (Finite {p : X.Point A // DomHolds p})

instance mapNonempty (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (X.Map A) :=
  let ⟨t, ρ, h⟩ := X.dom_nonempty A
  ⟨pt t ρ h⟩

end ExpExpansion

open FirstOrder

open Language Structure

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

end Lax480241.Expansions
end

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992
end Lax535992

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
end Lax535992.InflationaryFixedPoint.StepDef
end

-- Lax134656.PartialFixedPoint
section
namespace Lax134656
end Lax134656

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef
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

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax535992.LeastFixedPoint.Derives
end Lax535992.LeastFixedPoint.Derives

namespace Lax535992.LeastFixedPoint.LFPDef
end Lax535992.LeastFixedPoint.LFPDef
end

-- Lax480241.SecondOrderFixedPoints
section
namespace Lax480241.SecondOrderFixedPoints

open Lax134656.PartialFixedPoint Lax480241.Expansions Lax535992.LeastFixedPoint Lax904597.Problems

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-- An **order-free exponential expansion**: as
`ExpExpansion`, except that the domain sentence and the
defining sentences live over the bare vocabulary expanded by copies of the
block, with no order symbol available. Its universe is therefore defined on a
structure carrying no order. -/
structure ExpExpansionFree (L : Language.{0, 0}) : Type 1 where
  /-- The tags: finitely many copies of the space of block assignments. -/
  Tag : Type
  /-- Tags are finite, so that finite structures expand to finite
  structures. -/
  [tagFinite : Finite Tag]
  /-- The block whose assignments are the points of the expanded universe. -/
  B : SOBlock
  /-- The vocabulary of the expanded structure. -/
  E : Language.{0, 0}
  /-- The expanded vocabulary is relational, as every vocabulary of this
  library. -/
  [eRelational : E.IsRelational]
  /-- The domain sentence of each tag, over the bare vocabulary. -/
  dom : Tag → (L.sum B.lang).Sentence
  /-- The defining sentence of each relation symbol at each tuple of tags, over
  the bare vocabulary and as many copies of the block as the symbol has
  arguments. -/
  relSentence : ∀ {n : ℕ}, E.Relations n → (Fin n → Tag) →
    (L.sum (SOBlock.replicate B n).lang).Sentence
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (ρ : B.Assignment A),
      @Sentence.Realize _ A (SOBlock.structure₁ B (L := L) ρ) (dom t)

namespace ExpExpansionFree

variable (X : ExpExpansionFree L)

attribute [instance] tagFinite eRelational

/-- A candidate point: a tagged assignment of the block. -/
abbrev Point (A : Type) : Type := X.Tag × X.B.Assignment A

variable {X}

/-- The domain condition on a candidate point. -/
def DomHolds {A : Type} [L.Structure A] (p : X.Point A) : Prop :=
  @Sentence.Realize _ A (SOBlock.structure₁ X.B (L := L) p.2) (X.dom p.1)

variable (X)

/-- **The expanded universe**: the tagged block assignments satisfying their
tag's domain sentence. No order on `A` is involved. -/
def Map (A : Type) [L.Structure A] : Type := {p : X.Point A // DomHolds p}

variable {X}

variable (X)

/-- **The expanded structure.** -/
instance mapStructure (A : Type) [L.Structure A] : X.E.Structure (X.Map A) where
  funMap f := isEmptyElim f
  RelMap {n} r xs :=
    @Sentence.Realize _ A
      (SOBlock.structure₁ (SOBlock.replicate X.B n) (L := L)
        (SOBlock.replicateAssign X.B fun i => (xs i).1.2))
      (X.relSentence r fun i => (xs i).1.1)

instance mapFinite (A : Type) [L.Structure A] [Finite A] : Finite (X.Map A) :=
  inferInstanceAs (Finite {p : X.Point A // DomHolds p})

instance mapNonempty (A : Type) [L.Structure A] [Finite A] [Nonempty A] :
    Nonempty (X.Map A) :=
  let ⟨t, ρ, h⟩ := X.dom_nonempty A
  ⟨⟨(t, ρ), h⟩⟩

end ExpExpansionFree

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

end Lax480241.SecondOrderFixedPoints
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax480241.ExponentialClasses
section
namespace Lax480241.ExponentialClasses
end Lax480241.ExponentialClasses
end

-- Lax822549.WideMachines
section
namespace Lax822549.WideMachines.wpInp
end Lax822549.WideMachines.wpInp

namespace Lax822549.WideMachines.wpLe
end Lax822549.WideMachines.wpLe

namespace Lax822549.WideMachines

open Lax904597.Machines

open FirstOrder

open Language Structure

section Addresses

variable {α : Type}

/-- **The binary-number order on addresses**: the two subsets agree, or, at some
element where the first is out and the second in, they agree at every strictly
smaller element. Written with the strict order spelled out as
`Le y x ∧ ¬ Le x y`, which is the shape the defining sentence of the expansion
realizes to. -/
def WMSetLe (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  (∀ x, s x ↔ t x) ∨
    ∃ x, (∀ y, (Le y x ∧ ¬Le x y) → (s y ↔ t y)) ∧ ¬s x ∧ t x

/-- **The cell of an element on a file**: the initial segment it cuts among the
elements the file has a register for. The wide machine's register channel and
the wide tiling's bottom row are both described at these addresses – a *file* of
cells rather than the ruler of all the segments. -/
def WMFileSeg (Le : α → α → Prop) (Has : α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∀ y, s y ↔ (Le y x ∧ Has y)

end Addresses

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide-machine instances: the control of
`FirstOrder.Language.turing`, with the positions and their order replaced by an
order on the elements – the digits of an address. -/
inductive wideRel : ℕ → Type
  /-- `wmLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wideRel 2
  /-- `wmTr τ`: `τ` is a transition. -/
  | tr : wideRel 1
  /-- `wmStart q`: `q` is a start state. -/
  | start : wideRel 1
  /-- `wmAcc q`: `q` is an accepting state. -/
  | acc : wideRel 1
  /-- `wmBlank a`: `a` is the blank symbol. -/
  | blank : wideRel 1
  /-- `wmRight τ`: the transition `τ` moves the head right. -/
  | right : wideRel 1
  /-- `wmSrc τ q`: `τ` applies in the state `q`. -/
  | src : wideRel 2
  /-- `wmRead τ a`: `τ` applies when reading the symbol `a`. -/
  | read : wideRel 2
  /-- `wmDst τ q`: `τ` moves to the state `q`. -/
  | dst : wideRel 2
  /-- `wmWrite τ a`: `τ` writes the symbol `a`. -/
  | write : wideRel 2
  /-- `wmInp x a`: the address `{y | y ≤ x}` initially holds the symbol `a`. -/
  | inp : wideRel 2
  deriving DecidableEq

/-- The relational vocabulary of wide-machine instances. -/
def wide : Language :=
  ⟨fun _ => Empty, wideRel⟩

instance instIsRelationalWide : wide.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wide.Structure A]

end Shorthands

section Machine

variable (A : Type)

/-- **The universe of a wide machine**: the addresses – the subsets of the
instance, which are its tape cells and its time steps – together with the
elements of the instance, which are its control. An `abbrev`, so that the sum
structure stays visible to `rw` and to the elaborator. -/
abbrev WPoint : Type := (A → Prop) ⊕ A

variable {A} [wide.Structure A]

/-- Being a position: the addresses are the positions, the control elements are
not. -/
def wpPosn : WPoint A → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- A mark of the control, read on the universe of the machine: no address
carries it. -/
def wpMark (R : A → Prop) : WPoint A → Prop
  | Sum.inl _ => False
  | Sum.inr x => R x

/-- A binary attribute of the control, read on the universe of the machine. -/
def wpAttr (R : A → A → Prop) : WPoint A → WPoint A → Prop
  | Sum.inr x, Sum.inr y => R x y
  | _, _ => False

end Machine

open FirstOrder

open Language Structure

section RegCell

variable {A : Type} [wide.Structure A]

end RegCell

open Lax904597.Problems Lax485149.Problems

end Lax822549.WideMachines
end

-- Lax822549.WideRegChannel
section
namespace Lax822549.WideRegChannel
end Lax822549.WideRegChannel

namespace Lax822549.WideRegChannel.wpInpReg
end Lax822549.WideRegChannel.wpInpReg
end

-- Lax822549.WideTilings
section
namespace Lax822549.WideTilings

open Lax822549.WideMachines Lax904597.Machines

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

open FirstOrder

open Language Structure

/-- **A tile system**, read off an instance: the positions with their order,
the tiles with their compatibilities, the bottom row and the accepting tiles.
As with `TMData`, the record is a plain bundle of
predicates, so everything about tilings is stated once and read at whatever
structure supplies them. -/
structure TileData (A : Type) where
  /-- Being a position – a column, and equally a row. -/
  Posn : A → Prop
  /-- The order on positions. -/
  Le : A → A → Prop
  /-- Being a tile. -/
  Tile : A → Prop
  /-- Being an accepting tile. -/
  Acc : A → Prop
  /-- The right neighbor may carry this tile. -/
  Horiz : A → A → Prop
  /-- The upper neighbor may carry this tile. -/
  Vert : A → A → Prop
  /-- The bottom row's cell in this column may carry this tile. -/
  First : A → A → Prop
  /-- Being a base tile: what a column the description says nothing about
  carries in the bottom row. -/
  Base : A → Prop
  /-- Being a start tile: what the corner of the grid carries. -/
  Start : A → Prop
  /-- Being a left-edge tile: what the leftmost column may carry. -/
  EdgeL : A → Prop
  /-- Being a right-edge tile: what the rightmost column may carry. -/
  EdgeR : A → Prop

namespace TileData

variable {A : Type} (T : TileData A)

/-- **The tiles the bottom row may carry in a column**: the ones the
description names there, and the base tiles in a column it names none. This is
`TMData.InitTape`'s device – a description of the row
rather than a listing – and it is what lets an expansion carry it. -/
def FirstTile (x t : A) : Prop :=
  T.First x t ∨ ((∀ u, ¬T.First x u) ∧ T.Base t)

/-- **A tiling of the square**: every cell carries a tile, the bottom row is one
the description allows, the two edge columns carry tiles allowed there,
horizontal and vertical neighbors are compatible, and some cell carries an
accepting tile.

The two **edge conditions** are what the classical border colors of a tiling
problem do. A condition on neighbors says nothing about a column with no
neighbor on one side, so without them a tile whose meaning is “something is
arriving from the left” could stand in the leftmost column, justified by nothing;
a machine drawn as a tiling would then grow a head out of nowhere. -/
def IsTiling (τ : A → A → A) : Prop :=
  (∀ x y, T.Posn x → T.Posn y → T.Tile (τ x y)) ∧
    (∀ x y, T.Posn x → MinPos T.Le T.Posn y →
      ((MinPos T.Le T.Posn x → T.Start (τ x y)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ x y)))) ∧
    (∀ x y, T.Posn y → MinPos T.Le T.Posn x → T.EdgeL (τ x y)) ∧
    (∀ x y, T.Posn y → MaxPos T.Le T.Posn x → T.EdgeR (τ x y)) ∧
    (∀ x x' y, SuccPos T.Le T.Posn x x' → T.Posn y → T.Horiz (τ x y) (τ x' y)) ∧
    (∀ x y y', T.Posn x → SuccPos T.Le T.Posn y y' → T.Vert (τ x y) (τ x y')) ∧
    ∃ x y, T.Posn x ∧ T.Posn y ∧ T.Acc (τ x y)

/-- **The square is tileable**: some assignment of tiles to cells is a tiling.
The assignment is a function on the whole universe – what it does off the grid
is not read, so nothing is lost by not restricting it. -/
def Tileable : Prop := ∃ τ : A → A → A, T.IsTiling τ

/-- **Well-formedness**, folded into the yes-instances exactly as
`TMData.WellFormed` is: the order is linear, and there is
a position to index the grid by. -/
def WellFormed : Prop := IsLinOrd T.Le ∧ ∃ p, T.Posn p

open FirstOrder

open Language Structure

variable {A : Type} (T : TileData A)

end TileData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of wide tile-system instances: the tiles of
`FirstOrder.Language.tiling` with their compatibilities, and the positions and
their order replaced by an order on the elements – the digits of an address. -/
inductive wtileRel : ℕ → Type
  /-- `wtLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wtileRel 2
  /-- `wtDig x`: `x` is a digit – one of the elements the grid's coordinates are
  subsets of. -/
  | dig : wtileRel 1
  /-- `wtTile t`: `t` is a tile. -/
  | tile : wtileRel 1
  /-- `wtAcc t`: `t` is an accepting tile. -/
  | tacc : wtileRel 1
  /-- `wtHoriz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : wtileRel 2
  /-- `wtVert t t'`: `t'` may stand immediately above `t`. -/
  | vert : wtileRel 2
  /-- `wtFirst x t`: the bottom row's cell of `x` may carry `t`. -/
  | first : wtileRel 2
  /-- `wtBase t`: `t` is a base tile – what the bottom row carries where the
  description says nothing. -/
  | base : wtileRel 1
  /-- `wtStart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : wtileRel 1
  /-- `wtEdgeL t`: `t` may stand in the leftmost column. -/
  | ledge : wtileRel 1
  /-- `wtEdgeR t`: `t` may stand in the rightmost column. -/
  | redge : wtileRel 1
  deriving DecidableEq

/-- The relational vocabulary of wide tile-system instances. -/
def wtile : Language :=
  ⟨fun _ => Empty, wtileRel⟩

instance instIsRelationalWtile : wtile.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

/-- The order on the elements of the instance. -/
abbrev wtLe : wtile.Relations 2 := .wle

/-- The digit symbol. -/
abbrev wtDig : wtile.Relations 1 := .dig

/-- The tile symbol. -/
abbrev wtTile : wtile.Relations 1 := .tile

/-- The accepting-tile symbol. -/
abbrev wtAcc : wtile.Relations 1 := .tacc

/-- The horizontal-compatibility symbol. -/
abbrev wtHoriz : wtile.Relations 2 := .horiz

/-- The vertical-compatibility symbol. -/
abbrev wtVert : wtile.Relations 2 := .vert

/-- The bottom-row symbol. -/
abbrev wtFirst : wtile.Relations 2 := .first

/-- The base-tile symbol. -/
abbrev wtBase : wtile.Relations 1 := .base

/-- The start-tile symbol. -/
abbrev wtStart : wtile.Relations 1 := .tstart

/-- The left-edge symbol. -/
abbrev wtEdgeL : wtile.Relations 1 := .ledge

/-- The right-edge symbol. -/
abbrev wtEdgeR : wtile.Relations 1 := .redge

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [wtile.Structure A]

/-- The order on the elements. -/
def WTLe (a b : A) : Prop := RelMap wtLe ![a, b]

/-- Being a digit: one of the elements the grid's coordinates are subsets of. -/
def WTDig (a : A) : Prop := RelMap wtDig ![a]

/-- Being a tile. -/
def WTTile (a : A) : Prop := RelMap wtTile ![a]

/-- Being an accepting tile. -/
def WTAcc (a : A) : Prop := RelMap wtAcc ![a]

/-- Horizontal compatibility. -/
def WTHoriz (a b : A) : Prop := RelMap wtHoriz ![a, b]

/-- Vertical compatibility. -/
def WTVert (a b : A) : Prop := RelMap wtVert ![a, b]

/-- The bottom row, at the cell of an element. -/
def WTFirst (a b : A) : Prop := RelMap wtFirst ![a, b]

/-- Being a base tile. -/
def WTBase (a : A) : Prop := RelMap wtBase ![a]

/-- Being a start tile. -/
def WTStart (a : A) : Prop := RelMap wtStart ![a]

/-- Being a left-edge tile: one the leftmost column may carry. -/
def WTEdgeL (a : A) : Prop := RelMap wtEdgeL ![a]

/-- Being a right-edge tile: one the rightmost column may carry. -/
def WTEdgeR (a : A) : Prop := RelMap wtEdgeR ![a]

/-- **An element the bottom row is described at**: one whose cell carries a
tile. These are the elements the file has cells for. -/
def WTHasFirst (a : A) : Prop := ∃ t : A, WTFirst a t

end Shorthands

section System

variable {A : Type} [wtile.Structure A]

/-- Being a position: an address is one exactly when it holds digits alone, so
the grid is indexed by the subsets of the *marked* part of the instance. That is
what leaves the instance room for its tiles: a tile is an element like any
other, and only the digits are coordinates. -/
def wtpPosn : WPoint A → Prop
  | Sum.inl s => ∀ x, s x → WTDig x
  | Sum.inr _ => False

/-- The order on the universe of the tiling: addresses first, in the
binary-number order they inherit from the instance's own order, then the tiles
in that same order. -/
def wtpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WTLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WTLe x y

/-- The bottom row: the cell of `x` – the segment `x` cuts among the elements
the description names – may carry the tiles of `x`, and every other address a
base tile. That is the same device as the register channel's input
(`wpInpReg`): a file of cells, not the ruler of all the
segments, because a clocked machine's tape is described the same way and that is
where this problem's hardness comes from. -/
def wtpFirst : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMFileSeg WTLe WTHasFirst s x ∧ WTFirst x y
  | _, _ => False

variable (A) in
/-- **The wide tile system an instance describes**: the tiles read off the
instance, the positions being the addresses. -/
def wideTileData : TileData (WPoint A) where
  Posn := wtpPosn
  Le := wtpLe
  Tile := wpMark WTTile
  Acc := wpMark WTAcc
  Horiz := wpAttr WTHoriz
  Vert := wpAttr WTVert
  First := wtpFirst
  Base := wpMark WTBase
  Start := wpMark WTStart
  EdgeL := wpMark WTEdgeL
  EdgeR := wpMark WTEdgeR

end System

open Lax904597.Problems Lax485149.Problems

/-- **Square tiling one exponential up.** -/
def WideTiling : DecisionProblem wtile :=
  DecisionProblem.ofPred fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).Tileable

end Lax822549.WideTilings
end

-- Lax822549.WideProblemsValues
section
namespace Lax822549.WideProblemsValues

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes Lax904597.Machines Lax485149.Problems
    Lax480241.ExponentialClasses

open Lax822549.WideMachines Lax822549.WideRegChannel Lax822549.WideTilings

/-- The problem holds exactly when its conditions do. -/
axiom wideTiling_iff :
  ∀ (A : Type) [wtile.Structure A],
    WideTiling A ↔ (wideTileData A).WellFormed ∧ (wideTileData A).Tileable

end Lax822549.WideProblemsValues
end
