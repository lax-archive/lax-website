-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic

-- Lax194892.PebbleTransducers
section
namespace Lax194892.PebbleTransducers

/-- What a pebble transducer sees: for every pebble on the stack, from the
bottom, the two adjacent letters and the pebbles in the same place. -/
abbrev PebbleView (A : Type) := List ((Option A × Option A) × List Bool)

/-- The view of the input from a stack of gaps. -/
def viewOf {A : Type} (w : List A) (st : List ℕ) : PebbleView A :=
  st.map (fun p => ((if p = 0 then none else w[p - 1]?, w[p]?),
    st.map (fun q => decide (q = p))))

/-- The actions of a pebble transducer. -/
inductive PebbleAction (B : Type) : Type
  /-- Output a letter. -/
  | out : B → PebbleAction B
  /-- Move the head right (`true`) or left (`false`). -/
  | move : Bool → PebbleAction B
  /-- Push a new pebble at the first gap. -/
  | push : PebbleAction B
  /-- Pop the topmost pebble. -/
  | pop : PebbleAction B
  /-- Terminate. -/
  | terminate : PebbleAction B

/-- A `k`-pebble transducer: a deterministic machine with a stack of at most `k`
pebbles pointing to gaps of the input. -/
structure Pebble (A B Q : Type) (k : ℕ) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Q → PebbleView A → Q × PebbleAction B

/-- A configuration: the state and the stack of gaps (from the bottom), or the
halting vertex. -/
inductive PebbleCfg (Q : Type) : Type
  | conf : Q → List ℕ → PebbleCfg Q
  | halt : PebbleCfg Q

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- One step: the produced output and the next configuration, undefined if the
head leaves the input, the stack bound is exceeded, or an empty stack is popped. -/
def stepCfg (M : Pebble A B Q k) (w : List A) : PebbleCfg Q → Option (List B × PebbleCfg Q)
  | PebbleCfg.halt => none
  | PebbleCfg.conf q st =>
      let r := M.step q (viewOf w st)
      match r.2 with
      | PebbleAction.out b => some ([b], PebbleCfg.conf r.1 st)
      | PebbleAction.terminate => some ([], PebbleCfg.halt)
      | PebbleAction.push =>
          if st.length < k then some ([], PebbleCfg.conf r.1 (st ++ [0])) else none
      | PebbleAction.pop =>
          if st = [] then none else some ([], PebbleCfg.conf r.1 st.dropLast)
      | PebbleAction.move dir =>
          match st.getLast? with
          | none => none
          | some p =>
              if dir then
                (if p < w.length then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p + 1]))
                 else none)
              else
                (if 0 < p then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p - 1]))
                 else none)

/-- Reachability in the configuration graph, recording the output. -/
inductive Reaches (M : Pebble A B Q k) (w : List A) :
    PebbleCfg Q → List B → PebbleCfg Q → Prop
  | refl (c : PebbleCfg Q) : Reaches M w c [] c
  | step {c c' c'' : PebbleCfg Q} {o o' : List B} :
      M.stepCfg w c = some (o, c') → Reaches M w c' o' c'' → Reaches M w c (o ++ o') c''

end Pebble

end Lax194892.PebbleTransducers
end

-- Lax194892.PebbleConfigurationEncoding
section
namespace Lax194892.PebbleConfigurationEncoding.RestrReaches
end Lax194892.PebbleConfigurationEncoding.RestrReaches

namespace Lax194892.PebbleConfigurationEncoding

open Lax194892.PebbleTransducers

/-- The pebbles of the stack `st` sitting in the gap `p`. -/
def ann (k : ℕ) (st : List ℕ) (p : ℕ) : Fin k → Bool := fun i => decide (st[(i : ℕ)]? = some p)

/-- A letter of the representation of a pair of configurations: the two states, the
input letter following the gap, and the pebbles of each configuration in the gap. -/
abbrev PairLetter (A Q : Type) (k : ℕ) := Q × Q × Option A × (Fin k → Bool) × (Fin k → Bool)

/-- The string representation of the pair of configurations `(q₁, sts)` and
`(q₂, stt)` of the input `w`: one letter per gap. -/
def pairEnc {A Q : Type} {k : ℕ} (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A) :
    List (PairLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q₁, q₂, w[p]?, ann k sts p, ann k stt p)

end Lax194892.PebbleConfigurationEncoding
end

-- Lax194892.PebbleReachability
section
namespace Lax194892.PebbleReachability

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- The encodings of pairs of configurations connected by a run form a regular
language. -/
axiom exists_regular_reachLang {A B Q : Type} {k : ℕ} [Finite A] [Finite Q] (M : Pebble A B Q k) :
    ∃ L : Language (PairLetter A Q k), L.IsRegular ∧
      ∀ (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A),
        (∀ p ∈ sts, p ≤ w.length) → (∀ p ∈ stt, p ≤ w.length) →
        sts.length ≤ k → stt.length ≤ k →
        (pairEnc q₁ q₂ sts stt w ∈ L ↔
          ∃ v, M.Reaches w (PebbleCfg.conf q₁ sts) v (PebbleCfg.conf q₂ stt))

end Lax194892.PebbleReachability
end
