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

-- Lax799700.CliqueFamily
section
namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.CliqueFamily.markedGraphRel
end Lax799700.CliqueFamily.markedGraphRel

namespace Lax799700.CliqueFamily.markedGraphRel.adj
end Lax799700.CliqueFamily.markedGraphRel.adj

namespace Lax799700.CliqueFamily.markedGraphRel.marked
end Lax799700.CliqueFamily.markedGraphRel.marked
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

/-- A relation is acyclic if no element is reachable from itself along a
nonempty path. -/
def AcyclicRel (R : A → A → Prop) : Prop :=
  ∀ x, ¬Relation.TransGen R x x

end Acyclicity

section Generic

variable {A : Type}

/-- An arc surviving the removal of the `Fp`-arcs: the arc is present and not
removed. -/
def UncutArc (Adjp : A → A → Prop) (Fp : A → A → Prop) (a b : A) : Prop :=
  Adjp a b ∧ ¬Fp a b

/-- Some set of arcs whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked pairs: “some feedback arc set
is at most as large as the marked relation”. -/
def FeedbackArcOn (Adjp : A → A → Prop) (Kp : A → A → Prop) : Prop :=
  ∃ F : A → A → Prop, AcyclicRel (UncutArc Adjp F) ∧
    {p : A × A | F p.1 p.2}.ncard ≤ {p : A × A | Kp p.1 p.2}.ncard

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

/-- An arc-marked digraph has a feedback arc set at most as large as its
marked relation. -/
def HasSmallFeedbackArcSet (A : Type) [markedArcGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackArcOn (MAGAdj (A := A)) (MAGMarked (A := A))

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem FeedbackArcSet: does the structure satisfy `HasSmallFeedbackArcSet`? -/
def FeedbackArcSet : DecisionProblem Lax799700.Feedback.markedArcGraph :=
  DecisionProblem.ofPred HasSmallFeedbackArcSet

end Lax799700.Feedback
end
