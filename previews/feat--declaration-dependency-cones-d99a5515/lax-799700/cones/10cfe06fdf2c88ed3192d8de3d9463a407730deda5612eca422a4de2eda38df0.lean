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

/-- `adj a b`: there is an edge from `a` to `b`. -/
abbrev mgAdj : markedGraph.Relations 2 :=
  .adj

/-- `marked a`: the element `a` belongs to the marked set. -/
abbrev mgMarked : markedGraph.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

end Generic

section Problems

section Shorthands

variable {A : Type} [markedGraph.Structure A]

/-- `adj a b`: there is an edge from `a` to `b`.  -/
def MGAdj {A : Type} [markedGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap mgAdj ![a0, a1]

/-- `marked a`: the element `a` belongs to the marked set.  -/
def MGMarked {A : Type} [markedGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap mgMarked ![a0]

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

/-- An arc surviving the removal of the `Cp`-vertices: both endpoints are
outside `Cp` and the arc is present. -/
def SurvivingArc (Adjp : A → A → Prop) (Cp : A → Prop) (a b : A) : Prop :=
  ¬Cp a ∧ ¬Cp b ∧ Adjp a b

/-- Some set of vertices whose removal makes the digraph acyclic is at most as
large as the number encoded by the `Kp`-marked elements: “some feedback vertex
set is at most as large as the marked set”. -/
def FeedbackOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, AcyclicRel (SurvivingArc Adjp C) ∧ {x | C x}.ncard ≤ {x | Kp x}.ncard

end Generic

section Problems

section Shorthands

variable {A : Type} [markedArcGraph.Structure A]

end Shorthands

/-- A marked graph has a feedback vertex set at most as large as its marked
set. (Finiteness of the universe is part of the property: cardinality
thresholds are only meaningful on finite structures.) -/
def HasSmallFeedbackSet (A : Type) [markedGraph.Structure A] : Prop :=
  Finite A ∧ FeedbackOn (MGAdj (A := A)) (MGMarked (A := A))

end Problems

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Feedback
end
