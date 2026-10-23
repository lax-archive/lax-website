-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite.Basic

-- Lax765601.Derivatives
section
namespace Lax765601.Derivatives

/-- The derivative `f(w_)` of `f`: the output `f` produces after having read `w`,
namely `v ↦ f (w v)` with the first `|w|` letters of the output removed. -/
def deriv {A B : Type} (f : List A → List B) (w : List A) : List A → List B :=
  fun v => (f (w ++ v)).drop w.length

end Lax765601.Derivatives
end

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is length preserving, i.e. letter-to-letter: the output has the length of
the input. -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

/-- `f` is prefix determined: the first `n` output letters depend only on the
first `n` input letters. -/
def PrefixDetermined {A B : Type} (f : List A → List B) : Prop :=
  ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n

end Lax765601.ElementaryProperties
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

end Mealy

/-- A string-to-string function is computed by a Mealy machine if it is the
semantics of a Mealy machine with a finite state space. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

end Lax765601.MealyMachine
end

-- Lax765601.MealyDerivatives
section
namespace Lax765601.MealyDerivatives

open Lax765601.MealyMachine Lax765601.ElementaryProperties Lax765601.Derivatives

/-- A function is computed by a Mealy machine if and only if it has finitely many
derivatives, is letter-to-letter, and its first `n` output letters depend only on
its first `n` input letters. -/
axiom isMealy_iff {A B : Type} (f : List A → List B) :
    IsMealy f ↔ (Set.range (deriv f)).Finite ∧ LengthPreserving f ∧ PrefixDetermined f

end Lax765601.MealyDerivatives
end
