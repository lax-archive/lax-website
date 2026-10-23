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
namespace Lax194892.ChildConfigurationGraphs.CGPath
end Lax194892.ChildConfigurationGraphs.CGPath

namespace Lax194892.ChildConfigurationGraphs.HeightGe
end Lax194892.ChildConfigurationGraphs.HeightGe

namespace Lax194892.ChildConfigurationGraphs.IsChildSeq
end Lax194892.ChildConfigurationGraphs.IsChildSeq

namespace Lax194892.ChildConfigurationGraphs.StrictAbove
end Lax194892.ChildConfigurationGraphs.StrictAbove

namespace Lax194892.ChildConfigurationGraphs.dest
end Lax194892.ChildConfigurationGraphs.dest

namespace Lax194892.ChildConfigurationGraphs

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- A vertex of a child configuration graph: a state and a gap. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- A letter of the representation of a configuration: the state, the input letter
following the gap, and the pebbles in the gap. -/
abbrev ConfLetter (A Q : Type) (k : ℕ) := Q × Option A × (Fin k → Bool)

/-- The direction of an edge: inside the column, one column right, one column left. -/
abbrev Dir := Option Bool

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

/-- The representation of the child that the vertex `v` stands for: the state of
`v`, the input letters and the fixed pebbles of the graph, and the moving pebble
in the column of `v`. -/
def confAt {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (v : Vtx Q) :
    List (ConfLetter A Q k) :=
  u.mapIdx fun j c => (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j)))

/-- The concatenation of the representations of the children, in order. -/
def cgOut {A Q : Type} {k : ℕ} (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) :
    List (ConfLetter A Q k) :=
  ((List.range (m + 1)).map fun t => confAt u (p t)).flatten

end Lax194892.ChildConfigurationGraphs
end
