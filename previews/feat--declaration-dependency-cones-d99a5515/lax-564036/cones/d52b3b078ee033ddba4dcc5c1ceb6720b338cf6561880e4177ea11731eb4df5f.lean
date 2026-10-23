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

-- Lax564036.SatUnsat
section
namespace Lax564036.SatUnsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of *pairs* of CNF instances: two copies of
the symbols of CNF instances, one per side. -/
inductive satPairRel : ℕ → Type
  /-- `isClause₁ c`: `c` is a clause of the first formula. -/
  | isClause₁ : satPairRel 1
  /-- `posIn₁ c x`: `x` occurs positively in the first formula's clause `c`. -/
  | posIn₁ : satPairRel 2
  /-- `negIn₁ c x`: `x` occurs negatively in the first formula's clause `c`. -/
  | negIn₁ : satPairRel 2
  /-- `isClause₂ c`: `c` is a clause of the second formula. -/
  | isClause₂ : satPairRel 1
  /-- `posIn₂ c x`: `x` occurs positively in the second formula's clause `c`. -/
  | posIn₂ : satPairRel 2
  /-- `negIn₂ c x`: `x` occurs negatively in the second formula's clause `c`. -/
  | negIn₂ : satPairRel 2
  deriving DecidableEq

/-- The relational vocabulary of pairs of CNF instances. -/
def satPair : Language :=
  ⟨fun _ => Empty, satPairRel⟩

instance instIsRelationalSatPair : IsRelational satPair := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- “Is a clause of the first formula”. -/
abbrev spIsCl₁ : satPair.Relations 1 := .isClause₁

/-- “Occurs positively in”, first formula. -/
abbrev spPos₁ : satPair.Relations 2 := .posIn₁

/-- “Occurs negatively in”, first formula. -/
abbrev spNeg₁ : satPair.Relations 2 := .negIn₁

/-- “Is a clause of the second formula”. -/
abbrev spIsCl₂ : satPair.Relations 1 := .isClause₂

/-- “Occurs positively in”, second formula. -/
abbrev spPos₂ : satPair.Relations 2 := .posIn₂

/-- “Occurs negatively in”, second formula. -/
abbrev spNeg₂ : satPair.Relations 2 := .negIn₂

open FirstOrder

open Language Structure

section Defs

variable (A : Type) [satPair.Structure A]

/-- Satisfiability of the side of the instance read by the given triple of
symbols: some assignment of truth values makes every clause of that side
contain a true literal. Both sides of SAT-UNSAT are instances of this. -/
def SatWith (isCl : satPair.Relations 1)
    (pos neg : satPair.Relations 2) : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap isCl ![c] →
    ∃ x : A, (RelMap pos ![c, x] ∧ ν x) ∨ (RelMap neg ![c, x] ∧ ¬ν x)

end Defs

/-- SAT-UNSAT: the first formula of the pair is satisfiable and the second is
not. -/
def SATUNSAT : DecisionProblem satPair :=
  DecisionProblem.ofPred fun A _ =>
    SatWith A spIsCl₁ spPos₁ spNeg₁ ∧ ¬SatWith A spIsCl₂ spPos₂ spNeg₂

end Lax564036.SatUnsat
end
