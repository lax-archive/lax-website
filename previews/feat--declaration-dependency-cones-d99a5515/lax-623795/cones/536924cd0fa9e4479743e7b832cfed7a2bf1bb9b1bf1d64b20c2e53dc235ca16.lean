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

/-- A temporal graph is always connected when each of its snapshots is connected. -/
def AlwaysConnected {V : Type u} (G : TemporalGraph V) : Prop :=
  ∀ t, (G.snapshot t).Connected

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

/-- The first visit of `W`, or `none` when `W` is empty. -/
def startVisit? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Visit :=
  W.visits.head?

/-- The final visit of `W`, or `none` when `W` is empty. -/
def endVisit? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Visit :=
  W.visits.getLast?

/-- The starting vertex of `W`, or `none` when `W` is empty. -/
def startVertex? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option V :=
  W.startVisit?.map Visit.vertex

/-- The final vertex of `W`, or `none` when `W` is empty. -/
def endVertex? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option V :=
  W.endVisit?.map Visit.vertex

/-- Every visit of `W` occurs in the inclusive interval from `startTime` to `endTime`. -/
def IsWithin {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk)
    (startTime endTime : G.Timestep) : Prop :=
  ∀ visit ∈ W.visits,
    startTime.val.val ≤ visit.timestep.val.val ∧
      visit.timestep.val.val ≤ endTime.val.val

end TemporalWalk

/--
The vertices reachable within `[startTime, endTime]` from at least one vertex in `X`.
-/
def reachableVertexSet {V : Type u} (G : TemporalGraph V) (X : Set V)
    (startTime endTime : G.Timestep) : Set V :=
  { finish | ∃ start ∈ X, ∃ W : G.TemporalWalk,
      W.startVertex? = some start ∧
      W.endVertex? = some finish ∧
      W.IsWithin startTime endTime }

end TemporalGraph

end Lax623795.TemporalGraphs
end

-- Lax623795.TemporalExploration
section
universe u

namespace Lax623795.TemporalExploration

open Lax623795.TemporalGraphs

/-- Extending a reachability interval by one connected snapshot discovers a new vertex. -/
axiom reachableVertexSet_ssubset_next
    {V : Type u} (G : TemporalGraph V) (X : Set V)
    (startTime endTime nextTime : G.Timestep)
    (h_connected : G.AlwaysConnected)
    (hX_nonempty : X.Nonempty)
    (_hX_proper : X ≠ Set.univ)
    (h_interval : startTime.val.val ≤ endTime.val.val)
    (h_next : nextTime.val.val = endTime.val.val + 1)
    (h_reachable_proper :
      G.reachableVertexSet X startTime endTime ≠ Set.univ) :
    G.reachableVertexSet X startTime endTime ⊂
      G.reachableVertexSet X startTime nextTime

end Lax623795.TemporalExploration
end
