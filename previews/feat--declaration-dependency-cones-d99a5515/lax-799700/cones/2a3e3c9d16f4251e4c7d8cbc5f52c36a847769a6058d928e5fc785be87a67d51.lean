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

-- Lax799700.Steiner
section
namespace Lax799700.Steiner

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive steinerGraphRel : ℕ → Type where
/-- `adj a b`: there is an edge between `a` and `b`. -/
  | adj : steinerGraphRel 2
/-- `terminal a`: the vertex `a` must be spanned. -/
  | terminal : steinerGraphRel 1
/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
  | marked : steinerGraphRel 1
  deriving DecidableEq

/-- The relational language of graphs with terminals: adjacency, a set of
terminals to be spanned, and a marked set whose cardinality is the budget of
non-terminals. -/
def steinerGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, steinerGraphRel⟩

instance instIsRelationalSteinerGraph : FirstOrder.Language.IsRelational steinerGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `adj a b`: there is an edge between `a` and `b`. -/
abbrev stAdj : steinerGraph.Relations 2 :=
  .adj

/-- `terminal a`: the vertex `a` must be spanned. -/
abbrev stTerminal : steinerGraph.Relations 1 :=
  .terminal

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
  threshold. -/
abbrev stMarked : steinerGraph.Relations 1 :=
  .marked

open FirstOrder

open Language Structure

section Connectivity

variable {A : Type}

/-- The edges available inside a chosen set: adjacency in either direction,
restricted to the set. -/
def Link (Adjp : A → A → Prop) (S : A → Prop) (a b : A) : Prop :=
  S a ∧ S b ∧ (Adjp a b ∨ Adjp b a)

/-- A set of vertices is connected if any two of its members are joined by a
path inside it. -/
def ConnectedOn (Adjp : A → A → Prop) (S : A → Prop) : Prop :=
  ∀ x y, S x → S y → Relation.ReflTransGen (Link Adjp S) x y

end Connectivity

section Generic

variable {A : Type}

/-- Some connected set contains every terminal and uses at most as many
non-terminals as the number encoded by the marked set. -/
def SteinerOn (Adjp : A → A → Prop) (Term Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard ≤ {x | Kp x}.ncard

variable {B : Type}

end Generic

section Problem

section Shorthands

variable {A : Type} [steinerGraph.Structure A]

/-- `adj a b`: there is an edge between `a` and `b`.  -/
def STAdj {A : Type} [steinerGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stAdj ![a0, a1]

/-- `terminal a`: the vertex `a` must be spanned.  -/
def STTerminal {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stTerminal ![a0]

/-- `marked a`: the vertex `a` belongs to the marked set carrying the
threshold.  -/
def STMarked {A : Type} [steinerGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap stMarked ![a0]

end Shorthands

variable (A : Type) [steinerGraph.Structure A]

/-- A graph with terminals admits a connected set spanning the terminals and
using at most as many non-terminals as its marked set has elements.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSteinerTree : Prop :=
  Finite A ∧ SteinerOn (STAdj (A := A)) STTerminal STMarked

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem SteinerTree: does the structure satisfy `HasSmallSteinerTree`? -/
def SteinerTree : DecisionProblem Lax799700.Steiner.steinerGraph :=
  DecisionProblem.ofPred HasSmallSteinerTree

end Lax799700.Steiner
end
