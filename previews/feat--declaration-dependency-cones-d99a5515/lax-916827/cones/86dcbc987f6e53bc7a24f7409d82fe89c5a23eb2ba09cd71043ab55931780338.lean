-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax916827.TwoWayTransducers
section
namespace Lax916827.TwoWayTransducers.TwoWay.Reaches
end Lax916827.TwoWayTransducers.TwoWay.Reaches

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

/-- The configuration of the run on `w` after `n` steps; `none` once the run has
halted or got stuck. -/
def cfgAt (M : TwoWay A B Q) (w : List A) : ℕ → Option (Cfg A Q)
  | 0 => some (Cfg.conf [] M.init w)
  | n + 1 => (cfgAt M w n).bind fun c => (M.stepCfg c).map Prod.snd

/-- A configuration lies on the run of `M` on `w`. -/
def Visits (M : TwoWay A B Q) (w : List A) (c : Cfg A Q) : Prop := ∃ n, cfgAt M w n = some c

end TwoWay

end Lax916827.TwoWayTransducers
end

-- Lax916827.ConfigurationGraphs
section
namespace Lax916827.ConfigurationGraphs.TwoWay.emptyOut
end Lax916827.ConfigurationGraphs.TwoWay.emptyOut

namespace Lax916827.ConfigurationGraphs.TwoWay.pathTrans
end Lax916827.ConfigurationGraphs.TwoWay.pathTrans

namespace Lax916827.ConfigurationGraphs.TwoWay.readL
end Lax916827.ConfigurationGraphs.TwoWay.readL

namespace Lax916827.ConfigurationGraphs.TwoWay.readR
end Lax916827.ConfigurationGraphs.TwoWay.readR

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

/-- The label of the edge produced by a transition. -/
def labOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : Lab M :=
  ⟨transOut M l q r, ⟨(l, q, r), rfl⟩⟩

/-- The outgoing edge recorded, in the direction `d`, for the state `q` at a gap
with adjacent letters `l` and `r`: the left copy of a slice records the
transitions moving right, the right copy those moving left, and a halting
transition is recorded on both copies of its gap. -/
def edgeOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) (d : Bool) : VOut Q (Lab M) :=
  match M.step l q r with
  | Sum.inl _ => VOut.halt (labOf M l q r)
  | Sum.inr (q', _, dir) => if dir = d then VOut.move q' (labOf M l q r) else VOut.nil

/-- The letter to the left of the gap `j` of `w`, if any. -/
def prevAt (w : List A) (j : ℕ) : Option A := if j = 0 then none else w[j - 1]?

open scoped Classical in
/-- The outgoing edge, in the direction `d`, of the state `q` at the gap `j` of
`w`, for the *reachable* configurations only: a configuration the run does not
visit has no edge. -/
noncomputable def cutV (M : TwoWay A B Q) (w : List A) (j : ℕ) (q : Q) (d : Bool) :
    VOut Q (Lab M) :=
  if M.Visits w (Cfg.conf (w.take j) q (w.drop j)) then edgeOf M (prevAt w j) q w[j]? d
  else VOut.nil

variable {L : Type}

end TwoWay

end Lax916827.ConfigurationGraphs
end
