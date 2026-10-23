-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.Data.PNat.Notation

-- Lax623795.TemporalGraphs
section
namespace Lax623795.TemporalGraphs.TemporalGraph.TemporalWalk.CanConcat
end Lax623795.TemporalGraphs.TemporalGraph.TemporalWalk.CanConcat

universe u

namespace Lax623795.TemporalGraphs

/--
A finite-lifetime temporal graph on the vertex type `V`.

The positive natural number `lifetime` is the final time step. The snapshots are
indexed consecutively by the positive times `1, ..., lifetime`.
Each snapshot is the undirected, loop-free simple graph whose edges are
active at that time. The vertex type `V` is not required to be finite.
-/
structure TemporalGraph (V : Type u) where
  lifetime : ℕ+
  snapshot : { t : ℕ+ // t.val ≤ lifetime.val } → SimpleGraph V

namespace TemporalGraph

/-- A valid positive time step during the lifetime of `G`. -/
abbrev Timestep {V : Type u} (G : TemporalGraph V) :=
  { t : ℕ+ // t.val ≤ G.lifetime.val }

/-- Two vertices are adjacent in `G` at time `t`. -/
def AdjAt {V : Type u} (G : TemporalGraph V)
    (t : G.Timestep) (x y : V) : Prop :=
  (G.snapshot t).Adj x y

/-- A visit records the vertex occupied by a walk at a particular time step. -/
structure Visit {V : Type u} (G : TemporalGraph V) where
  vertex : V
  timestep : G.Timestep

/-- `next` may follow `current` when time increases and the walk waits or traverses an edge. -/
def IsValidSuccessor {V : Type u} (G : TemporalGraph V)
    (current next : G.Visit) : Prop :=
  current.timestep.val.val < next.timestep.val.val ∧
    (current.vertex = next.vertex ∨
      G.AdjAt next.timestep current.vertex next.vertex)

/--
A temporal walk is a chain of timed vertex visits.

Times strictly increase. Between consecutive visits the walk either remains at the
same vertex or traverses an edge active at the later time. The empty list is the
temporal walk with no visited vertices.
-/
structure TemporalWalk {V : Type u} (G : TemporalGraph V) where
  visits : List G.Visit
  chain : visits.IsChain (G.IsValidSuccessor)

namespace TemporalWalk

/-- The instantaneous temporal walk consisting of one visit. -/
def singleton {V : Type u} (G : TemporalGraph V)
    (v : V) (t : G.Timestep) : G.TemporalWalk where
  visits := [⟨v, t⟩]
  chain := .singleton _

end TemporalWalk

end TemporalGraph

end Lax623795.TemporalGraphs
end
