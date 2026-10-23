-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate

-- Lax765601.Aperiodicity
section
namespace Lax765601.Aperiodicity

/-- The `n`-fold concatenation `vⁿ` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

/-- A string-to-string function is aperiodic if for all input strings `u, v, w` the
last letter of `f (u vⁿ w)` — as an element of `Option B`, so that "no letter" is
an admissible value — is the same for all sufficiently large `n`. -/
def Aperiodic {A B : Type} (f : List A → List B) : Prop :=
  ∀ u v w : List A, ∃ o : Option B, ∃ N : ℕ, ∀ n ≥ N, (f (u ++ npow v n ++ w)).getLast? = o

end Lax765601.Aperiodicity
end

-- Lax765601.MealyMachine
section
namespace Lax765601.MealyMachine

/-- A Mealy machine with input alphabet `A`, output alphabet `B` and state space
`Q`: an initial state and a transition function `Q × A → Q × B`. -/
structure Mealy (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a source state and an input letter determine a
  target state and an output letter. -/
  step : Q → A → Q × B

namespace Mealy

variable {A B Q : Type}

/-- The output produced by the machine on an input string, when started in a
given state. -/
def run (M : Mealy A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (M.step q a).2 :: M.run (M.step q a).1 w

/-- The semantics of a Mealy machine: the output produced from the initial state.
-/
def eval (M : Mealy A B Q) (w : List A) : List B := M.run M.init w

/-- The underlying pre-automaton: the transition function with the output letters
forgotten. -/
def transFun (M : Mealy A B Q) : Q → A → Q := fun q a => (M.step q a).1

end Mealy

/-- A string-to-string function is computed by a Mealy machine if it is the
semantics of a Mealy machine with a finite state space. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

end Lax765601.MealyMachine
end

-- Lax765601.StateTransformations
section
namespace Lax765601.StateTransformations

open Lax765601.MealyMachine

/-- The state transformation of an input string, for the pre-automaton `δ`: the
letters act one after the other, in reading order. -/
def strTrans {A Q : Type} (δ : Q → A → Q) (w : List A) : Q → Q := fun q => w.foldl δ q

/-- The stabilisation condition (*) of Lemma A.2.11: for every state
transformation `δ_w` arising from an input string, the sequence of its powers
`δ_w¹, δ_w², …` eventually stabilises. -/
def TransAperiodic {A Q : Type} (δ : Q → A → Q) : Prop :=
  ∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, (strTrans δ w)^[n] = (strTrans δ w)^[N]

end Lax765601.StateTransformations
end

-- Lax765601.AperiodicityMinimalMachine
section
namespace Lax765601.AperiodicityMinimalMachine

open Lax765601.MealyMachine Lax765601.StateTransformations Lax765601.Aperiodicity

/-- A Mealy function is aperiodic if and only if some Mealy machine computing it
satisfies the stabilisation condition (*) on its state transformations. -/
axiom aperiodic_iff_transAperiodic {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ TransAperiodic M.transFun

end Lax765601.AperiodicityMinimalMachine
end
