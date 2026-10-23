-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

-- Lax825442.ChromaticNumber
section
namespace Lax825442.ChromaticNumber

/-- The natural-valued chromatic number of a finite graph. -/
noncomputable def chromaticNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

end Lax825442.ChromaticNumber
end
