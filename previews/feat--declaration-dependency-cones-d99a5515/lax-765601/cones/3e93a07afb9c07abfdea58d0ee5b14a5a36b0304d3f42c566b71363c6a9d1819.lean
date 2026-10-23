-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.SetTheory.Cardinal.Finite

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

end Mealy

end Lax765601.MealyMachine
end

-- Lax765601.MealyEquivalenceBound
section
namespace Lax765601.MealyEquivalenceBound

open Lax765601.MealyMachine

/-- Two Mealy machines are equivalent if and only if they agree on every input
string of length at most the product of their numbers of states. -/
axiom eval_eq_iff_short {A B Q₁ Q₂ : Type} [Finite Q₁] [Finite Q₂]
    (M : Mealy A B Q₁) (N : Mealy A B Q₂) :
    M.eval = N.eval ↔
      ∀ w : List A, w.length ≤ Nat.card Q₁ * Nat.card Q₂ → M.eval w = N.eval w

end Lax765601.MealyEquivalenceBound
end
