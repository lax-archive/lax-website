-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

-- Lax194892.PebbleTransducers
section
namespace Lax194892.PebbleTransducers.Pebble.Reaches
end Lax194892.PebbleTransducers.Pebble.Reaches

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

end Pebble

end Lax194892.PebbleTransducers
end

-- Lax194892.PebbleConfigurationEncoding
section
namespace Lax194892.PebbleConfigurationEncoding
end Lax194892.PebbleConfigurationEncoding

namespace Lax194892.PebbleConfigurationEncoding.RestrReaches
end Lax194892.PebbleConfigurationEncoding.RestrReaches
end

-- Lax194892.ChildConfigurationGraphs
section
namespace Lax194892.ChildConfigurationGraphs.CGLetter
end Lax194892.ChildConfigurationGraphs.CGLetter

namespace Lax194892.ChildConfigurationGraphs.CGPath
end Lax194892.ChildConfigurationGraphs.CGPath

namespace Lax194892.ChildConfigurationGraphs.IsChildSeq
end Lax194892.ChildConfigurationGraphs.IsChildSeq

namespace Lax194892.ChildConfigurationGraphs.dest
end Lax194892.ChildConfigurationGraphs.dest

namespace Lax194892.ChildConfigurationGraphs

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- The stack has height at least `h`; the halting vertex has no height. -/
def HeightGe {Q : Type} (h : ℕ) : PebbleCfg Q → Prop
  | PebbleCfg.conf _ st => h ≤ st.length
  | PebbleCfg.halt => False

/-- A run of at least one step whose intermediate configurations have height at
least `h`. -/
inductive StrictAbove {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (h : ℕ) :
    PebbleCfg Q → PebbleCfg Q → Prop
  /-- A single step. -/
  | one {c c' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → StrictAbove M w h c c'
  /-- A step to a configuration of height at least `h`, followed by such a run. -/
  | cons {c c' c'' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → HeightGe h c' →
      StrictAbove M w h c' c'' → StrictAbove M w h c c''

/-- A vertex of a child configuration graph: a state and a gap. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- The configuration of the child `v` of a configuration with stack `st`: the
moving pebble sits on top. -/
def cfgOf {Q : Type} (st : List ℕ) (v : Vtx Q) : PebbleCfg Q := PebbleCfg.conf v.1 (st ++ [v.2])

/-- `v'` is the child following the child `v`: the run from `v` first returns to
the children's height at `v'`. -/
def NextChild {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (st : List ℕ)
    (v v' : Vtx Q) : Prop :=
  StrictAbove M w (st.length + 2) (cfgOf st v) (cfgOf st v')

end Lax194892.ChildConfigurationGraphs
end
