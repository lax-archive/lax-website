-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

/-- A path in the automaton, given as the list of the transitions it uses. -/
inductive Path (M : LabAut A L Q) : Q → List (Q × List A × L × Q) → Q → Prop
  | nil (q : Q) : Path M q [] q
  | cons {q : Q} {u : List A} {l : L} {q' : Q} {ts : List (Q × List A × L × Q)} {p : Q} :
      (q, u, l, q') ∈ M.δ → Path M q' ts p → Path M q ((q, u, l, q') :: ts) p

/-- The input string of a path: the concatenation of the input strings of its
transitions. -/
def inputOf (ts : List (Q × List A × L × Q)) : List A := (ts.map (fun t => t.2.1)).flatten

/-- The labels along a path, in the order of the transitions. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

/-- A path is accepting if it starts in an initial state and ends in a final state.
-/
def Accepting (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) : Prop :=
  ∃ q ∈ M.init, ∃ p ∈ M.final, M.Path q ts p

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations

open Lax132576.LabelledAutomata

/-- A nondeterministic automaton with output: a labelled automaton whose labels
are output strings. -/
abbrev NFAO (A B Q : Type) := LabAut A (List B) Q

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path: the concatenation of the outputs of its
transitions. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B := (LabAut.labelsOf ts).flatten

/-- The relation computed by an automaton with output: `w` is related to `v` if
some accepting run reads `w` and writes `v`. -/
def rel (M : NFAO A B Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

end NFAO

/-- A relation is rational if it is computed by a nondeterministic automaton with
output with a finite state space. -/
def IsRationalRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), ∀ w v, R w v ↔ M.rel w v

end Lax132576.RationalRelations
end

-- Lax132576.RationalFunctions
section
namespace Lax132576.RationalFunctions

open Lax132576.RationalRelations

/-- A string-to-string function is rational if its graph is a rational relation.
-/
def IsRationalFun {A B : Type} (f : List A → List B) : Prop :=
  IsRationalRel (fun w v => v = f w)

end Lax132576.RationalFunctions
end

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

/-- The slice of the reachable configuration graph of `M` on `w` at the letter of
position `i`. -/
noncomputable def encSlice (M : TwoWay A B Q) (w : List A) (i : ℕ) : Slice Q (Lab M) :=
  fun v => cutV M w (if v.1 then i + 1 else i) v.2 (!v.1)

/-- The special letter for the empty input: the output of the halting transition on
the empty input, if the run on the empty input halts at once. -/
def emptyOut (M : TwoWay A B Q) : Option (Lab M) :=
  match M.step none M.init none with
  | Sum.inl _ => some (labOf M none M.init none)
  | Sum.inr _ => none

/-- The string representation of the reachable configuration graph of `M` on `w`:
one slice per input letter, and the special letter for the empty input. -/
noncomputable def enc (M : TwoWay A B Q) (w : List A) : List (CLet Q (Lab M)) :=
  if w.isEmpty then [Sum.inr (emptyOut M)]
  else (List.range w.length).map (fun i => Sum.inl (encSlice M w i))

variable {L : Type}

end TwoWay

end Lax916827.ConfigurationGraphs
end

-- Lax916827.ConfigurationGraphRational
section
namespace Lax916827.ConfigurationGraphRational

open Lax132576.RationalFunctions Lax916827.TwoWayTransducers Lax916827.ConfigurationGraphs

/-- The string representation of the reachable configuration graph is a rational
function of the input. -/
axiom isRationalFun_enc {A B Q : Type} [Finite A] [Finite Q] (M : TwoWay A B Q) :
    IsRationalFun (TwoWay.enc M)

end Lax916827.ConfigurationGraphRational
end
