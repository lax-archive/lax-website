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

end Lax799700.MaxCut
end
