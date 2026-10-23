-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Hom.Set
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
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

-- Lax366625.CountingProblems
section
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

/-- The counting problem given by a number attached to every structure: the
least value it takes on the structures isomorphic to a given one, which is
invariant by construction. When the number is itself invariant, this is the
number. -/
noncomputable def ofFun (f : ∀ (A : Type) [L.Structure A], ℕ) : CountingProblem L where
  Count := fun A _ =>
    sInf {n : ℕ | ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @f B i = n}
  iso_invariant := fun e =>
    congrArg sInf (Set.ext fun _ =>
      ⟨fun ⟨B, i, g, h⟩ => ⟨B, i, e.comp g, h⟩, fun ⟨B, i, g, h⟩ => ⟨B, i, e.symm.comp g, h⟩⟩)

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

end Lax366625.CountingProblems
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

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.Steiner
end

-- Lax280166.CountingSteinerTrees
section
namespace Lax280166.CountingSteinerTrees

open Lax799700.Steiner

open FirstOrder

open Language Structure

section Generic

variable {A B : Type}

/-- The set `S` contains every terminal, is connected, and has exactly as many
non-terminals as the `Kp`-marked set has elements. -/
def SteinerOfSizeOn (Adjp : A → A → Prop) (Term Kp : A → Prop) (S : A → Prop) : Prop :=
  (∀ x, Term x → S x) ∧ ConnectedOn Adjp S ∧
    {x | S x ∧ ¬Term x}.ncard = {x | Kp x}.ncard

end Generic

section Problem

variable (A : Type) [steinerGraph.Structure A]

/-- The set `S` is a connected set containing every terminal and using exactly
as many non-terminals as the marked set has elements, in a finite graph. -/
def SteinerOfSize (S : A → Prop) : Prop :=
  Finite A ∧ SteinerOfSizeOn (fun a b : A => STAdj a b) (fun a => STTerminal a)
    (fun a => STMarked a) S

end Problem

open Lax366625.CountingProblems

/-- **#Steiner Tree**, as a counting problem. -/
noncomputable def SharpSteinerTree : CountingProblem Lax799700.Steiner.steinerGraph :=
  CountingProblem.ofFun fun A _ =>
    Nat.card {S : A → Prop // SteinerOfSize A S}

end Lax280166.CountingSteinerTrees
end
