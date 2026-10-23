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

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992.InflationaryFixedPoint

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[reducible]
def SOBlock.structure₁ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

/-- The all-empty assignment of a block: the starting point of the
iteration. -/
def SOBlock.botAssign (B : SOBlock) (A : Type) : B.Assignment A :=
  fun _ _ => False

/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence

namespace StepDef

variable {L : Language.{0, 0}} (d : StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

/-- One application of the step formulas to an assignment. -/
def next (ρ : d.B.Assignment A) : d.B.Assignment A :=
  fun i x => @Formula.Realize _ A (SOBlock.structure₁ (L := L) d.B ρ) _ (d.step i) x

end Semantics

end StepDef

end Lax535992.InflationaryFixedPoint
end

-- Lax134656.PartialFixedPoint
section
namespace Lax134656.PartialFixedPoint

open Lax535992.InflationaryFixedPoint Lax904597.Problems

open FirstOrder

open Language Structure

open Function (IsFixedPt)

namespace StepDef

section Semantics

variable {L : Language.{0, 0}} (d : StepDef L) {A : Type} [L.Structure A]

variable (A) in
/-- The stages of the partial iteration. -/
def partStage (n : ℕ) : d.B.Assignment A :=
  (d.next)^[n] (SOBlock.botAssign d.B A)

end Semantics

end StepDef

namespace StepDef

/-- The value of a simultaneous induction read partially: some stage is a
fixed point of the step and satisfies the output sentence. All stable stages
are equal, so this says exactly «the iteration converges and its limit
satisfies the output». -/
def PFPHolds {L : Language.{0, 0}} (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  ∃ n, IsFixedPt d.next (partStage d A n) ∧
    @Sentence.Realize _ A (SOBlock.structure₁ (L := L) d.B (partStage d A n)) d.out

end StepDef

/-- A decision problem is *FO(≤, PFP) definable* if, on nonempty finite
ordered structures, it is the value of a simultaneous induction over the
ordered expansion of its vocabulary, read partially – for every linear order,
the problem itself never seeing it. -/
def PFPDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef (L.sum Language.order),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ StepDef.PFPHolds d A

end Lax134656.PartialFixedPoint
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

/-- **SO(≤, PFP)**: a partial fixed point over a second-order universe. The
order the expansion's own sentences read can be removed
(`sopfpDefinable_iff_free`), by guessing it into the
block. -/
def SOPFPDefinable (P : DecisionProblem L) : Prop :=
  ∃ (X : ExpExpansion L) (Q : DecisionProblem X.E), PFPDefinable Q ∧
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A], P A ↔ Q (X.Map A)

end Lax480241.SecondOrderFixedPoints
end
