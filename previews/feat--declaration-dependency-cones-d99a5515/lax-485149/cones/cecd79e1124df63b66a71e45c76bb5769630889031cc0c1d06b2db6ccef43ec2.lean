-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Semantics

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

-- Lax485149.Complement
section
namespace Lax485149.Complement

open Lax904597.Problems

open FirstOrder

open Language

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

end Lax485149.Complement
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

-- Lax485149.Reachability
section
namespace Lax485149.Reachability

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open Lax904597.Problems Lax485149.Problems Lax485149.Complement

/-- The relation symbols of graphs with marked sources and targets. -/
inductive stGraphRel : ℕ → Type where
  /-- `edge a b`: there is an edge from `a` to `b`. -/
  | edge : stGraphRel 2
  /-- `source a`: the vertex `a` is a marked source. -/
  | source : stGraphRel 1
  /-- `target a`: the vertex `a` is a marked target. -/
  | target : stGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of directed graphs with marked sources and
targets. -/
def stGraph : Language :=
  ⟨fun _ => Empty, stGraphRel⟩

instance instIsRelationalStGraph : IsRelational stGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `edge a b`: there is an edge from `a` to `b`. -/
abbrev sgEdge : stGraph.Relations 2 := .edge

/-- `source a`: the vertex `a` is a marked source. -/
abbrev sgSource : stGraph.Relations 1 := .source

/-- `target a`: the vertex `a` is a marked target. -/
abbrev sgTarget : stGraph.Relations 1 := .target

/-- `edge a b`: there is an edge from `a` to `b`. -/
def SGEdge {A : Type} [stGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  RelMap sgEdge ![a0, a1]

/-- `source a`: the vertex `a` is a marked source. -/
def SGSource {A : Type} [stGraph.Structure A] (a0 : A) : Prop :=
  RelMap sgSource ![a0]

/-- `target a`: the vertex `a` is a marked target. -/
def SGTarget {A : Type} [stGraph.Structure A] (a0 : A) : Prop :=
  RelMap sgTarget ![a0]

/-- Some marked target is reachable from some marked source, along a
(possibly empty) directed path. -/
def Reachable (A : Type) [stGraph.Structure A] : Prop :=
  ∃ s t : A, SGSource s ∧ SGTarget t ∧ Relation.ReflTransGen SGEdge s t

/-- REACH: is some marked target reachable from some marked source? -/
def REACH : DecisionProblem stGraph := DecisionProblem.ofPred fun A _ => Reachable A

/-- UNREACH, the complement of REACH: no marked target is reachable from a
marked source. -/
def UNREACH : DecisionProblem stGraph := DecisionProblem.compl REACH

end Lax485149.Reachability
end
