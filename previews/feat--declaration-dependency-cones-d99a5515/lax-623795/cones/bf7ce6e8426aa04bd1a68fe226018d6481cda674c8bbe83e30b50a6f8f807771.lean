-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.Data.PNat.Notation

-- Lax623795.TemporalGraphs
section
namespace Lax623795.TemporalGraphs.TemporalGraph.Visit
end Lax623795.TemporalGraphs.TemporalGraph.Visit

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

/-- The static graph containing every edge that appears in any snapshot of `G`. -/
def footprint {V : Type u} (G : TemporalGraph V) : SimpleGraph V :=
  ⨆ t, G.snapshot t

namespace TemporalWalk

end TemporalWalk

end TemporalGraph

end Lax623795.TemporalGraphs
end
