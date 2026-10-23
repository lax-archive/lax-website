-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs

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

-- Lax916827.TwoWayTransducers
section
namespace Lax916827.TwoWayTransducers.TwoWay.cfgAt
end Lax916827.TwoWayTransducers.TwoWay.cfgAt

namespace Lax916827.TwoWayTransducers

/-- A two-way transducer: on the letters adjacent to the head and the state, it
either produces an output string and halts (`Sum.inl`), or produces an output
string, changes state and moves the head left (`false`) or right (`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

/-- A configuration: the input to the left of the head, the state, and the input
to the right of the head; or the halting vertex. -/
inductive Cfg (A Q : Type) : Type
  | conf : List A → Q → List A → Cfg A Q
  | halt : Cfg A Q

namespace TwoWay

variable {A B Q : Type}

/-- One step of the computation: the produced output and the next configuration,
if the head does not fall off the input. -/
def stepCfg (M : TwoWay A B Q) : Cfg A Q → Option (List B × Cfg A Q)
  | Cfg.halt => none
  | Cfg.conf u q v =>
      match M.step u.getLast? q v.head? with
      | Sum.inl o => some (o, Cfg.halt)
      | Sum.inr (q', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (o, Cfg.conf (u ++ [a]) q' v')
      | Sum.inr (q', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (o, Cfg.conf u.dropLast q' (a :: v))

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : TwoWay A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : Reaches M c [] c
  | step {c c' c'' : Cfg A Q} {o o' : List B} :
      M.stepCfg c = some (o, c') → Reaches M c' o' c'' → Reaches M c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`: the run from the
initial configuration reaches the halting vertex with output `v`. -/
def Computes (M : TwoWay A B Q) (w : List A) (v : List B) : Prop :=
  M.Reaches (Cfg.conf [] M.init w) v Cfg.halt

end TwoWay

/-- A function computed by a two-way transducer with a finite state space. -/
def IsTwoWay {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : TwoWay A B Q), ∀ w, M.Computes w (f w)

end Lax916827.TwoWayTransducers
end

-- Lax916827.TwoWayMealyPrecomposition
section
namespace Lax916827.TwoWayMealyPrecomposition

open Lax765601.MealyMachine Lax916827.TwoWayTransducers

/-- Pre-composing a two-way transducer with a Mealy machine gives a two-way
transducer. -/
axiom isTwoWay_comp_isMealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsMealy f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f)

end Lax916827.TwoWayMealyPrecomposition
end
