-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

-- Lax194892.PebbleTransducers
section
namespace Lax194892
end Lax194892

namespace Lax194892.PebbleTransducers
end Lax194892.PebbleTransducers

namespace Lax194892.PebbleTransducers.Pebble
end Lax194892.PebbleTransducers.Pebble

namespace Lax194892.PebbleTransducers.PebbleAction
end Lax194892.PebbleTransducers.PebbleAction

namespace Lax194892.PebbleTransducers.PebbleCfg
end Lax194892.PebbleTransducers.PebbleCfg

namespace Lax194892.PebbleTransducers.Pebble.Reaches
end Lax194892.PebbleTransducers.Pebble.Reaches

namespace Lax194892.PebbleTransducers.Pebble.stepCfg
end Lax194892.PebbleTransducers.Pebble.stepCfg

namespace Lax194892.PebbleTransducers.PebbleAction.move
end Lax194892.PebbleTransducers.PebbleAction.move

namespace Lax194892.PebbleTransducers.PebbleAction.out
end Lax194892.PebbleTransducers.PebbleAction.out

namespace Lax194892.PebbleTransducers.PebbleAction.pop
end Lax194892.PebbleTransducers.PebbleAction.pop

namespace Lax194892.PebbleTransducers.PebbleAction.push
end Lax194892.PebbleTransducers.PebbleAction.push

namespace Lax194892.PebbleTransducers.PebbleAction.terminate
end Lax194892.PebbleTransducers.PebbleAction.terminate

namespace Lax194892.PebbleTransducers.PebbleCfg.conf
end Lax194892.PebbleTransducers.PebbleCfg.conf

namespace Lax194892.PebbleTransducers.PebbleCfg.halt
end Lax194892.PebbleTransducers.PebbleCfg.halt
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
namespace Lax194892.ChildConfigurationGraphs.HeightGe
end Lax194892.ChildConfigurationGraphs.HeightGe

namespace Lax194892.ChildConfigurationGraphs.IsChildSeq
end Lax194892.ChildConfigurationGraphs.IsChildSeq

namespace Lax194892.ChildConfigurationGraphs.StrictAbove
end Lax194892.ChildConfigurationGraphs.StrictAbove

namespace Lax194892.ChildConfigurationGraphs

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- A vertex of a child configuration graph: a state and a gap. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- A letter of the representation of a configuration: the state, the input letter
following the gap, and the pebbles in the gap. -/
abbrev ConfLetter (A Q : Type) (k : ℕ) := Q × Option A × (Fin k → Bool)

/-- The direction of an edge: inside the column, one column right, one column left. -/
abbrev Dir := Option Bool

/-- The column that the direction `d` leads to from the column `p`. -/
def dest (p : ℕ) : Dir → Option ℕ
  | none => some p
  | some true => some (p + 1)
  | some false => if p = 0 then none else some (p - 1)

/-- A letter of the representation of a child configuration graph: one gap of the
input, with the input letter, the fixed pebbles, the index of the moving pebble,
the states that are the first child in this column, and the outgoing and
incoming edges of the vertices of this column. -/
structure CGLetter (A Q : Type) (k : ℕ) where
  /-- The input letter following this gap, absent for the last gap. -/
  lett : Option A
  /-- The fixed pebbles sitting in this gap. -/
  peb : Fin k → Bool
  /-- The index of the moving pebble. -/
  nid : Fin k
  /-- The states `q` for which `(q, this column)` is the first child. -/
  src : Q → Bool
  /-- The outgoing edge of `(q, this column)`. -/
  nxt : Q → Option (Q × Dir)
  /-- The incoming edge of `(q, this column)`. -/
  prv : Q → Option (Q × Dir)

/-- The vertex that the edge out of `v` leads to, if any. -/
def succOf {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) : Option (Vtx Q) :=
  (u[v.2]?).bind fun c => (c.nxt v.1).bind fun x => (dest v.2 x.2).map fun p' => (x.1, p')

/-- `v` is marked as the first child. -/
def IsSrc {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) : Prop :=
  ∃ c, u[v.2]? = some c ∧ c.src v.1 = true

/-- The representation of the child that the vertex `v` stands for: the state of
`v`, the input letters and the fixed pebbles of the graph, and the moving pebble
in the column of `v`. -/
def confAt {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) :
    List (ConfLetter A Q k) :=
  u.mapIdx fun j c => (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j)))

/-- The letter to the left of the gap `i`. -/
def leftLet {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (i : ℕ) : Option (CGLetter A Q k) :=
  if i = 0 then none else u[i - 1]?

open Classical in
/-- The local consistency test on two adjacent letters: every edge recorded by
`nxt` between or inside their columns is recorded by `prv` at its target, and a
vertex marked as the first child has no incoming edge. -/
noncomputable def pairOK {A Q : Type} {k : ℕ} (a b : Option (CGLetter A Q k)) : Bool := decide (
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → ca.nxt q = some (q', some true) →
      cb.prv q' = some (q, some true)) ∧
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → cb.nxt q = some (q', some false) →
      ca.prv q' = some (q, some false)) ∧
  (∀ q q' : Q, ∀ cb, b = some cb → cb.nxt q = some (q', none) → cb.prv q' = some (q, none)) ∧
  (∀ q : Q, ∀ cb, b = some cb → cb.src q = true → cb.prv q = none))

/-- The string is locally consistent at every gap. -/
def Chk {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) : Prop :=
  ∀ i ≤ u.length, pairOK (leftLet u i) u[i]? = true

/-- `p 0, …, p m` is the run of children described by the locally consistent
string `u`: `p 0` is the unique first child, each `p (t+1)` is reached from `p t`
by the recorded edge, and `p m` has no outgoing edge. -/
structure CGPath {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) :
    Prop where
  /-- The string is locally consistent. -/
  chk : Chk u
  /-- `p 0` is the unique vertex marked as the first child. -/
  srcEq : ∀ v, IsSrc u v ↔ v = p 0
  /-- Every vertex of the run sits in a real column. -/
  inRange : ∀ t ≤ m, (u[(p t).2]?).isSome
  /-- Consecutive children are joined by the recorded edge. -/
  step : ∀ t < m, succOf u (p t) = some (p (t + 1))
  /-- The last child has no outgoing edge. -/
  last : succOf u (p m) = none

/-- The concatenation of the representations of the children, in order. -/
def cgOut {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) :
    List (ConfLetter A Q k) :=
  ((List.range (m + 1)).map fun t => confAt u (p t)).flatten

/-- `v` is the string representation of the children of the configuration whose
child configuration graph `u` represents. -/
def CGOutIs {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : List (ConfLetter A Q k)) :
    Prop :=
  ∃ m p, CGPath u m p ∧ v = cgOut u m p

end Lax194892.ChildConfigurationGraphs
end
