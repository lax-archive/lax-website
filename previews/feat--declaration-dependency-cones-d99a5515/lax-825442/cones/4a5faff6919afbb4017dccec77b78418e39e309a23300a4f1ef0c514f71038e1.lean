-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

-- Lax825442.VertexCliqueCover
section
namespace Lax825442.VertexCliqueCover

/-- The vertex clique cover number, expressed as the chromatic number of the
complement. -/
noncomputable def vertexCliqueCover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Gᶜ.chromaticNumber.toNat

end Lax825442.VertexCliqueCover
end
