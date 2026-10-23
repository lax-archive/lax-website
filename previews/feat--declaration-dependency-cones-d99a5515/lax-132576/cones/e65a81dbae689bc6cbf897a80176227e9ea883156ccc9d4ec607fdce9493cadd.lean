-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.ConditionallyCompleteLattice.Basic

-- Lax132576.LeftDistance
section
namespace Lax132576.LeftDistance

/-- The left distance `‖w₁, w₂‖`: the least `k` such that `w₁ = v v₁` and
`w₂ = v v₂` with `|v₁|, |v₂| ≤ k`. -/
noncomputable def leftDist {B : Type} (w₁ w₂ : List B) : ℕ :=
  sInf {k : ℕ | ∃ v v₁ v₂ : List B,
    w₁ = v ++ v₁ ∧ w₂ = v ++ v₂ ∧ v₁.length ≤ k ∧ v₂.length ≤ k}

/-- A partial function has bounded variation if for all `w₁, w₂` the left distances
`‖f (w w₁), f (w w₂)‖` are bounded, over the `w` for which both are defined. -/
def BoundedVariation {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
    f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K

end Lax132576.LeftDistance
end

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

/-- The transition function of the underlying automaton. -/
def transFun (T : Sequential A B Q) : Q → A → Q := fun q a => (T.step q a).1

end Sequential

end Lax132576.SequentialTransducers
end

-- Lax765601.MealyMachine
section
namespace Lax765601
end Lax765601

namespace Lax765601.MealyMachine
end Lax765601.MealyMachine

namespace Lax765601.MealyMachine.Mealy
end Lax765601.MealyMachine.Mealy

namespace Lax765601.MealyMachine.Mealy.run
end Lax765601.MealyMachine.Mealy.run
end

-- Lax765601.StateTransformations
section
namespace Lax765601.StateTransformations

open Lax765601.MealyMachine

/-- The state transformation of an input string, for the pre-automaton `δ`: the
letters act one after the other, in reading order. -/
def strTrans {A Q : Type} (δ : Q → A → Q) (w : List A) : Q → Q := fun q => w.foldl δ q

end Lax765601.StateTransformations
end

-- Lax132576.SubsequentialTransducers
section
namespace Lax132576.SubsequentialTransducers

open Lax765601.StateTransformations Lax132576.SequentialTransducers

/-- A subsequential transducer: a sequential transducer with a partial end-of-input
function applied to the last state of the run. -/
structure Subsequential (A B Q : Type) extends Sequential A B Q where
  /-- The partial end-of-input function. -/
  endOfInput : Q → Option (List B)

namespace Subsequential

variable {A B Q : Type}

/-- The semantics of a subsequential transducer: the output of the sequential
part followed by the end-of-input value, when defined. -/
def eval (T : Subsequential A B Q) (w : List A) : Option (List B) :=
  (T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init)).map
    (fun u => T.toSequential.eval w ++ u)

end Subsequential

/-- A partial function computed by a subsequential transducer with a finite state
space. -/
def IsSubsequential {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Subsequential A B Q), T.eval = f

end Lax132576.SubsequentialTransducers
end

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A partial function is continuous if, for every regular language `L` over the
output alphabet, the set of input strings whose output is defined and belongs to
`L` is regular. -/
def PartialContinuous {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, f w = some v ∧ v ∈ L} : Language A)

end Lax765601.Continuity
end

-- Lax132576.SubsequentialCharacterisation
section
namespace Lax132576.SubsequentialCharacterisation

open Lax765601.Continuity Lax132576.SubsequentialTransducers Lax132576.LeftDistance

/-- A partial function is subsequential if and only if it is continuous and has
bounded variation. -/
axiom isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔ PartialContinuous f ∧ BoundedVariation f

end Lax132576.SubsequentialCharacterisation
end
