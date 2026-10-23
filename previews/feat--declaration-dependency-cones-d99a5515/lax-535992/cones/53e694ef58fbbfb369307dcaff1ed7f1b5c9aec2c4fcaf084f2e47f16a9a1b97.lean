-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax535992.Game
section
namespace Lax535992.Game

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive andOrGraphRel : ℕ → Type where
/-- `move a b`: the player to move at `a` may move to `b`. -/
  | move : andOrGraphRel 2
/-- `univ a`: the node `a` belongs to the universal player. -/
  | univ : andOrGraphRel 1
/-- `start a`: the node `a` is a marked starting position. -/
  | start : andOrGraphRel 1
/-- `won a`: the node `a` wins outright. -/
  | won : andOrGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of AND/OR graphs: a move relation, a mark for the
nodes of the universal player, a mark for the starting positions and a mark for
the positions that win outright. -/
def andOrGraph : FirstOrder.Language :=
  ⟨fun _ => Empty, andOrGraphRel⟩

instance instIsRelationalAndOrGraph : FirstOrder.Language.IsRelational andOrGraph := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `move a b`: the player to move at `a` may move to `b`. -/
abbrev agMove : andOrGraph.Relations 2 :=
  .move

/-- `univ a`: the node `a` belongs to the universal player. -/
abbrev agUniv : andOrGraph.Relations 1 :=
  .univ

/-- `start a`: the node `a` is a marked starting position. -/
abbrev agStart : andOrGraph.Relations 1 :=
  .start

/-- `won a`: the node `a` wins outright. -/
abbrev agWon : andOrGraph.Relations 1 :=
  .won

open FirstOrder

open Language Structure

section Defs

variable {A : Type} [andOrGraph.Structure A]

/-- `move a b`: the player to move at `a` may move to `b`.  -/
def AGMove {A : Type} [andOrGraph.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agMove ![a0, a1]

/-- `univ a`: the node `a` belongs to the universal player.  -/
def AGUniv {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agUniv ![a0]

/-- `start a`: the node `a` is a marked starting position.  -/
def AGStart {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agStart ![a0]

/-- `won a`: the node `a` wins outright.  -/
def AGWon {A : Type} [andOrGraph.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap agWon ![a0]

variable (A) in
/-- **The winning positions of an AND/OR graph**, as a least fixed point: a
position that wins outright, an existential position with a winning successor,
or a universal position that has a successor and all of whose successors
win. -/
inductive WinsOn : A → Prop
  /-- A position that wins outright. -/
  | won {a : A} : AGWon a → WinsOn a
  /-- An existential position with a winning successor. -/
  | ex {a b : A} : ¬AGUniv a → AGMove a b → WinsOn b → WinsOn a
  /-- A universal position with a successor, all of whose successors win. -/
  | all {a : A} : AGUniv a → (∃ b, AGMove a b) → (∀ b, AGMove a b → WinsOn b) → WinsOn a

variable (A) in
/-- Some marked starting position is winning. -/
def GameWon : Prop := ∃ s : A, AGStart s ∧ WinsOn A s

end Defs

/-- GAME, alternating reachability: does the existential player win from some
starting position? -/
def GAME : DecisionProblem andOrGraph := DecisionProblem.ofPred fun A _ => GameWon A

end Lax535992.Game
end
