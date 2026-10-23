-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

-- Lax153141.MixedMinorNumber
section
namespace Lax153141.MixedMinorNumber.Division
end Lax153141.MixedMinorNumber.Division

namespace Lax153141.MixedMinorNumber

/-- The adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Prop :=
  fun i j => G.Adj (e i) (e j)

end Lax153141.MixedMinorNumber
end
