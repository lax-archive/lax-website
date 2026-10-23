-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Infix

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A string-to-string function is *continuous* if the inverse image of every
regular language over the output alphabet is a regular language. -/
def Continuous {A B : Type} (f : List A → List B) : Prop :=
  ∀ L : Language B, L.IsRegular → Language.IsRegular ({w : List A | f w ∈ L} : Language A)

end Lax765601.Continuity
end

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is prefix preserving: `w ⊑ v` implies `f w ⊑ f v`. -/
def PrefixPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w v : List A, w <+: v → f w <+: f v

/-- `f` is length preserving, i.e. letter-to-letter: the output has the length of
the input. -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

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

-- Lax132576.MealyMachineIndependent
section
namespace Lax132576.MealyMachineIndependent

open Lax765601.Continuity Lax765601.ElementaryProperties Lax765601.MealyMachine

/-- A function is computed by a Mealy machine if and only if it is continuous,
prefix preserving and length preserving. -/
axiom isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f

end Lax132576.MealyMachineIndependent
end
