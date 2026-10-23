-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Infix

-- Lax132576.SequentialTransducers
section
namespace Lax132576.SequentialTransducers

/-- A sequential transducer: a Mealy machine whose transitions produce output
strings of variable length. -/
structure Sequential (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a target state and an output string. -/
  step : Q → A → Q × List B

namespace Sequential

variable {A B Q : Type}

/-- The output produced from a given state on an input string. -/
def run (T : Sequential A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (T.step q a).2 ++ T.run (T.step q a).1 w

/-- The semantics of a sequential transducer. -/
def eval (T : Sequential A B Q) (w : List A) : List B := T.run T.init w

end Sequential

/-- A function computed by a sequential transducer with a finite state space. -/
def IsSequential {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Sequential A B Q), T.eval = f

end Lax132576.SequentialTransducers
end

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

end Lax765601.ElementaryProperties
end

-- Lax132576.SequentialCharacterisation
section
namespace Lax132576.SequentialCharacterisation

open Lax765601.Continuity Lax765601.ElementaryProperties Lax132576.SequentialTransducers

/-- A function is sequential if and only if it maps `ε` to `ε`, is continuous,
prefix preserving, and has bounded increase. -/
axiom isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K

end Lax132576.SequentialCharacterisation
end
