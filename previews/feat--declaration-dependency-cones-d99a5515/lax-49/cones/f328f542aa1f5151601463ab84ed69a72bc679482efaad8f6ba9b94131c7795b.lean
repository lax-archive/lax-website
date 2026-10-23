-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

-- Lax49.MixedMinorNumber
section
namespace Lax49.MixedMinorNumber.Division
end Lax49.MixedMinorNumber.Division

namespace Lax49.MixedMinorNumber

/-- The adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Prop :=
  fun i j => G.Adj (e i) (e j)

end Lax49.MixedMinorNumber
end
