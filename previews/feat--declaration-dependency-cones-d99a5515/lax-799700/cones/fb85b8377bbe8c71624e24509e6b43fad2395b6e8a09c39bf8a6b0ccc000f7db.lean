-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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

-- Lax799700.CliqueFamily
section
namespace Lax799700.CliqueFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedGraphRel : ℕ → Type where
/-- `adj a b`: there is an edge from `a` to `b`. -/
  | adj : markedGraphRel 2
/-- `marked a`: the element `a` belongs to the marked set. -/
  | marked : markedGraphRel 1
  deriving DecidableEq

/-- The relational language of marked graphs: a graph together with a marked
subset of its vertices, whose cardinality serves as threshold. -/
def markedGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, markedGraphRel⟩

instance instIsRelationalMarkedGraph : FirstOrder.Language.IsRelational markedGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

end Generic

section Problems

section Shorthands

variable {A : Type} [markedGraph.Structure A]

end Shorthands

variable (A : Type) [markedGraph.Structure A]

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.CliqueFamily
end

-- Lax799700.Feedback
section
namespace Lax799700.Feedback

open Lax799700.CliqueFamily

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive markedArcGraphRel : ℕ → Type where
/-- `adj a b`: there is an arc from `a` to `b`. -/
  | adj : markedArcGraphRel 2
/-- `marked a b`: the pair `(a, b)` belongs to the marked relation. -/
  | marked : markedArcGraphRel 2
  deriving DecidableEq

/-- The relational language of arc-marked digraphs: a digraph together with a
marked binary relation, whose cardinality (as a set of pairs) serves as
threshold. -/
def markedArcGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, markedArcGraphRel⟩

instance instIsRelationalMarkedArcGraph : FirstOrder.Language.IsRelational markedArcGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `adj a b`: there is an arc from `a` to `b`. -/
abbrev magAdj : markedArcGraph.Relations 2 :=
  .adj

/-- `marked a b`: the pair `(a, b)` belongs to the marked relation. -/
abbrev magMarked : markedArcGraph.Relations 2 :=
  .marked

open FirstOrder

open Language Structure

section Acyclicity

variable {A : Type}

end Acyclicity

section Generic

variable {A : Type}

end Generic

section Problems

section Shorthands

variable {A : Type} [markedArcGraph.Structure A]

/-- `adj a b`: there is an arc from `a` to `b`.  -/
def MAGAdj {A : Type} [markedArcGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap magAdj ![a0, a1]

/-- `marked a b`: the pair `(a, b)` belongs to the marked relation.  -/
def MAGMarked {A : Type} [markedArcGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap magMarked ![a0, a1]

end Shorthands

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Feedback
end

-- Lax799700.MaxCut
section
namespace Lax799700.MaxCut

open Lax799700.Feedback

open FirstOrder

open Language Structure

section Semantics

variable {A : Type}

/-- The cut determined by `S`, as a relation: `a` is adjacent to `b`, `a` lies
inside `S` and `b` outside. Reading the cut as a set of ordered pairs of this
shape counts every cut edge of a symmetric adjacency relation once. -/
def CutRel (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ S a ∧ ¬S b

/-- Some cut is at least as large as the number encoded by the `Kp`-marked
pairs: “some cut has at least `k` edges”. -/
def MaxCutOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ S : A → Prop,
    {p : A × A | Kp p.1 p.2}.ncard ≤ {p : A × A | CutRel Adjp S p.1 p.2}.ncard

end Semantics

section Problem

/-- An arc-marked graph has a cut at least as large as its marked relation.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeCut (A : Type) [markedArcGraph.Structure A] : Prop :=
  Finite A ∧ MaxCutOn (MAGAdj (A := A)) (MAGMarked (A := A))

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem MaxCut: does the structure satisfy `HasLargeCut`? -/
def MaxCut : DecisionProblem Lax799700.Feedback.markedArcGraph :=
  DecisionProblem.ofPred HasLargeCut

/-- The yes-instances of MaxCut are exactly the structures satisfying
`HasLargeCut`. -/
axiom maxCut_iff : ∀ (A : Type) [Lax799700.Feedback.markedArcGraph.Structure A], MaxCut A ↔ HasLargeCut A

end Lax799700.MaxCut
end
