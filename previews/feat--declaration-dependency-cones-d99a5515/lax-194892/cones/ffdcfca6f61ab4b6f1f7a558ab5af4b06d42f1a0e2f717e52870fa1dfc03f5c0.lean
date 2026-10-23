-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Basic

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
namespace Lax194892.PebbleConfigurationEncoding.RestrReaches
end Lax194892.PebbleConfigurationEncoding.RestrReaches

namespace Lax194892.PebbleConfigurationEncoding

open Lax194892.PebbleTransducers

/-- The pebbles of the stack `st` sitting in the gap `p`. -/
def ann (k : ℕ) (st : List ℕ) (p : ℕ) : Fin k → Bool := fun i => decide (st[(i : ℕ)]? = some p)

end Lax194892.PebbleConfigurationEncoding
end

-- Lax194892.ChildConfigurationGraphs
section
namespace Lax194892.ChildConfigurationGraphs.CGLetter
end Lax194892.ChildConfigurationGraphs.CGLetter

namespace Lax194892.ChildConfigurationGraphs.CGPath
end Lax194892.ChildConfigurationGraphs.CGPath

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

/-- `v` is the first child of the configuration `(q, st)`. -/
def FirstChild {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ)
    (v : Vtx Q) : Prop :=
  StrictAbove M w (st.length + 2) (PebbleCfg.conf q st) (cfgOf st v)

/-- `ch 0, …, ch m` is the list of the children of `(q, st)`, in order of
execution. -/
structure IsChildSeq {A B Q : Type} {k : ℕ} (M : Pebble A B Q k) (w : List A) (q : Q)
    (st : List ℕ) (ch : ℕ → Vtx Q) (m : ℕ) : Prop where
  /-- The list starts with the first child. -/
  first : FirstChild M w q st (ch 0)
  /-- Each child is followed by the next one. -/
  next : ∀ t < m, NextChild M w st (ch t) (ch (t + 1))
  /-- The last child has no successor. -/
  stop : ∀ v, ¬ NextChild M w st (ch m) v

/-- A letter of the representation of a configuration: the state, the input letter
following the gap, and the pebbles in the gap. -/
abbrev ConfLetter (A Q : Type) (k : ℕ) := Q × Option A × (Fin k → Bool)

/-- The string representation of the configuration `(q, st)` of `w`: one letter per
gap. -/
def confEnc {A Q : Type} {k : ℕ} (q : Q) (st : List ℕ) (w : List A) : List (ConfLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q, w[p]?, ann k st p)

end Lax194892.ChildConfigurationGraphs
end

-- Lax194892.ForTransducers
section
namespace Lax194892.ForTransducers.ForProg.LoopFree
end Lax194892.ForTransducers.ForProg.LoopFree

namespace Lax194892.ForTransducers.ForProg.nestLoops
end Lax194892.ForTransducers.ForProg.nestLoops

namespace Lax194892.ForTransducers

/-- Tests of a for-transducer. -/
inductive ForTest (A : Type) : Type
  /-- The value of a Boolean variable. -/
  | boolVar : ℕ → ForTest A
  /-- The equality test `x == y` on position variables. -/
  | eqPos : ℕ → ℕ → ForTest A
  /-- The order test `x <= y` on position variables. -/
  | lePos : ℕ → ℕ → ForTest A
  /-- The label test `w[x] == a`. -/
  | label : ℕ → A → ForTest A
  /-- Negation. -/
  | not : ForTest A → ForTest A
  /-- Conjunction. -/
  | and : ForTest A → ForTest A → ForTest A
  /-- Disjunction. -/
  | or : ForTest A → ForTest A → ForTest A

/-- Programs of a for-transducer. -/
inductive ForProg (A B : Type) : Type
  /-- The empty program. -/
  | skip : ForProg A B
  /-- `output(b)`. -/
  | output : B → ForProg A B
  /-- `X = true` / `X = false`. -/
  | assign : ℕ → Bool → ForProg A B
  /-- Sequential composition `I ; J`. -/
  | seq : ForProg A B → ForProg A B → ForProg A B
  /-- A conditional. -/
  | ite : ForTest A → ForProg A B → ForProg A B → ForProg A B
  /-- `for x in positions(w)` (`true`) or `for x in positions_reverse(w)` (`false`). -/
  | loop : Bool → ℕ → ForProg A B → ForProg A B

namespace ForTest

variable {A : Type}

/-- The truth value of a test under valuations of the position and Boolean
variables. -/
def Holds (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) : ForTest A → Prop
  | boolVar i => bv i = true
  | eqPos i j => pos i = pos j
  | lePos i j => pos i ≤ pos j
  | label i a => w[pos i]? = some a
  | not t => ¬ Holds w pos bv t
  | and t s => Holds w pos bv t ∧ Holds w pos bv s
  | or t s => Holds w pos bv t ∨ Holds w pos bv s

end ForTest

/-- Running the body of a loop over a list of positions, threading the Boolean
valuation and concatenating the outputs. -/
def forLoopRun {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) :
    List ℕ → (ℕ → Bool) → (ℕ → Bool) × List B
  | [], bv => (bv, [])
  | p :: ps, bv =>
      let r := body bv p
      let r' := forLoopRun body ps r.1
      (r'.1, r.2 ++ r'.2)

namespace ForProg

variable {A B : Type}

open scoped Classical in
/-- The semantics of a program: the final Boolean valuation and the output. -/
noncomputable def exec (w : List A) :
    ForProg A B → (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool) × List B
  | skip, _, bv => (bv, [])
  | output b, _, bv => (bv, [b])
  | assign i v, _, bv => (Function.update bv i v, [])
  | seq P Q, pos, bv =>
      let r := exec w P pos bv
      let r' := exec w Q pos r.1
      (r'.1, r.2 ++ r'.2)
  | ite t P Q, pos, bv =>
      if ForTest.Holds w pos bv t then exec w P pos bv else exec w Q pos bv
  | loop dir x P, pos, bv =>
      forLoopRun (fun bv' p => exec w P (Function.update pos x p) bv')
        (if dir then List.range w.length else (List.range w.length).reverse) bv

/-- The function computed by a for-transducer. -/
noncomputable def eval (P : ForProg A B) (w : List A) : List B :=
  (exec w P (fun _ => 0) (fun _ => false)).2

end ForProg

/-- A function computed by a for-transducer. -/
def IsForTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ∀ w, P.eval w = f w

end Lax194892.ForTransducers
end

-- Lax194892.ChildrenOfConfiguration
section
namespace Lax194892.ChildrenOfConfiguration

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding
  Lax194892.ChildConfigurationGraphs Lax194892.ForTransducers

/-- A for-transducer maps the representation of a configuration to the
concatenation of the representations of its children. -/
axiom exists_forTransducer_children {A B Q : Type} [Finite A] [Finite Q] {k : ℕ}
    (M : Pebble A B Q k) :
    ∃ f : List (ConfLetter A Q k) → List (ConfLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → Vtx Q) (m : ℕ),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k →
        IsChildSeq M w q₀ st ch m →
        f (confEnc q₀ st w)
          = ((List.range (m + 1)).map fun t => confEnc (ch t).1 (st ++ [(ch t).2]) w).flatten

end Lax194892.ChildrenOfConfiguration
end
