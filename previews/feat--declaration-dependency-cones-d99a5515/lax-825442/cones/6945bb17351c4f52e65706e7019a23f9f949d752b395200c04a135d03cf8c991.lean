-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.VertexCover

-- Lax825442.VertexCover
section
namespace Lax825442.VertexCover

/-- The natural-valued vertex-cover number of a finite graph. -/
noncomputable def vertexCover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  G.vertexCoverNum.toNat

end Lax825442.VertexCover
end
