-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax916827.TwoWayTransducers
section
namespace Lax916827.TwoWayTransducers.Cfg
end Lax916827.TwoWayTransducers.Cfg

namespace Lax916827.TwoWayTransducers.Cfg.conf
end Lax916827.TwoWayTransducers.Cfg.conf

namespace Lax916827.TwoWayTransducers.Cfg.halt
end Lax916827.TwoWayTransducers.Cfg.halt

namespace Lax916827.TwoWayTransducers.TwoWay.Reaches
end Lax916827.TwoWayTransducers.TwoWay.Reaches

namespace Lax916827.TwoWayTransducers.TwoWay.cfgAt
end Lax916827.TwoWayTransducers.TwoWay.cfgAt

namespace Lax916827.TwoWayTransducers.TwoWay.stepCfg
end Lax916827.TwoWayTransducers.TwoWay.stepCfg

namespace Lax916827.TwoWayTransducers

/-- A two-way transducer: on the letters adjacent to the head and the state, it
either produces an output string and halts (`Sum.inl`), or produces an output
string, changes state and moves the head left (`false`) or right (`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

namespace TwoWay

variable {A B Q : Type}

end TwoWay

end Lax916827.TwoWayTransducers
end

-- Lax916827.ConfigurationGraphs
section
namespace Lax916827.ConfigurationGraphs.TwoWay.emptyOut
end Lax916827.ConfigurationGraphs.TwoWay.emptyOut

namespace Lax916827.ConfigurationGraphs

open Lax916827.TwoWayTransducers

/-- The outgoing edge of a vertex inside one slice: none, an edge to the state `q'`
of the other copy labelled `l`, or the halting vertex with the output `l`. -/
inductive VOut (Q L : Type) where
  /-- No outgoing edge inside this slice. -/
  | nil : VOut Q L
  /-- An edge to the state `q'` of the other copy, labelled `l`. -/
  | move (q' : Q) (l : L) : VOut Q L
  /-- The transducer halts here, producing `l`. -/
  | halt (l : L) : VOut Q L

/-- A slice of the configuration graph at a letter: the outgoing edge of every
vertex, `(false, q)` being the state `q` at the gap to the left of the letter and
`(true, q)` at the gap to its right. -/
abbrev Slice (Q L : Type) := Bool × Q → VOut Q L

/-- The alphabet `C`: the slices, and the special letter for the empty input,
carrying the output of the halting transition on the empty input if the run
halts there. -/
abbrev CLet (Q L : Type) := Slice Q L ⊕ Option L

namespace TwoWay

variable {A B Q : Type}

/-- The output string produced by a transition. -/
def transOut (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : List B :=
  match M.step l q r with
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

/-- The output strings occurring in the transition function. -/
def OutLabels (M : TwoWay A B Q) : Set (List B) :=
  Set.range (fun p : Option A × Q × Option A => transOut M p.1 p.2.1 p.2.2)

/-- The finite set of edge labels: the output strings of the transitions. -/
abbrev Lab (M : TwoWay A B Q) : Type := {o : List B // o ∈ OutLabels M}

variable {L : Type}

/-- The outgoing edge at the current gap recorded by the letter to the right of
the head. -/
def readR (r : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match r with
  | some (Sum.inl s) => s (false, q)
  | some (Sum.inr (some lab)) => VOut.halt lab
  | _ => VOut.nil

/-- The outgoing edge at the current gap recorded by the letter to the left of the
head. -/
def readL (l : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match l with
  | some (Sum.inl s) => s (true, q)
  | _ => VOut.nil

/-- The two-way transducer over `C` that walks along the path of a represented
configuration graph, printing the labels of the edges it follows; on a string
that represents nothing it halts with empty output. -/
def pathTrans (M : TwoWay A B Q) : TwoWay (CLet Q (Lab M)) B Q where
  init := M.init
  step := fun l q r =>
    match readR r q with
    | VOut.move q' lab => Sum.inr (q', lab.val, true)
    | VOut.halt lab => Sum.inl lab.val
    | VOut.nil =>
      match readL l q with
      | VOut.move q' lab => Sum.inr (q', lab.val, false)
      | VOut.halt lab => Sum.inl lab.val
      | VOut.nil => Sum.inl []

end TwoWay

end Lax916827.ConfigurationGraphs
end
