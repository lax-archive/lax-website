-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finite.Defs

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

end Lax916827.TwoWayTransducers
end

-- Lax916827.TwoWayCodes
section
namespace Lax916827.TwoWayCodes

open Lax916827.TwoWayTransducers

/-- A code of a two-way transducer over `ℕ`: a lookup table from triples (letter to
the left, state, letter to the right) to transitions. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

/-- The two-way transducer described by a code: initial state `0`, and the table
entry of a triple, or halting with empty output when the triple is absent. -/
def twoWayCodeAut (c : TwoWayCode) : TwoWay ℕ ℕ ℕ where
  init := 0
  step := fun l q r =>
    match c.lookup (l, q, r) with
    | some x => x
    | none => Sum.inl []

/-- The relation computed by the coded transducer. -/
def twoWayCodeRel (c : TwoWayCode) : List ℕ → List ℕ → Prop := (twoWayCodeAut c).Computes

/-- The coded transducer computes a total function: it halts on every input. -/
def TwoWayCodeTotal (c : TwoWayCode) : Prop := ∀ w, ∃ v, twoWayCodeRel c w v

end Lax916827.TwoWayCodes
end
