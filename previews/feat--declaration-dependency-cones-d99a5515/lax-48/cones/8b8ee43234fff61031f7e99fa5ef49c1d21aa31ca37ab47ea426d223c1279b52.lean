-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax48.TwinWidth
section
namespace Lax48.TwinWidth.PartitionSequence
end Lax48.TwinWidth.PartitionSequence

namespace Lax48.TwinWidth

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

end Lax48.TwinWidth
end
