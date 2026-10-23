-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs

-- Lax17.Degree
section
namespace Lax17
end Lax17

namespace Lax17.Degree
end Lax17.Degree
end

-- Lax17.SpanningTreeRounding
section
namespace Lax17.SpanningTreeRounding.FeasiblePoint
end Lax17.SpanningTreeRounding.FeasiblePoint

namespace Lax17.SpanningTreeRounding

universe u

open Finset

/-- The finite edge set of `G`. -/
noncomputable def edges {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

/-- The edges of `G` incident with `v`. -/
noncomputable def incidentEdges {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (Sym2 V) :=
  (edges G).filter fun e => v ∈ e

end Lax17.SpanningTreeRounding
end
