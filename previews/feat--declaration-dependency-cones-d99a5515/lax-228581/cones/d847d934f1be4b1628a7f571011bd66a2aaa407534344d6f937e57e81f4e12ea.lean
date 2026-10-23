-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax228581.TwinWidth
section
namespace Lax228581.TwinWidth.PartitionSequence
end Lax228581.TwinWidth.PartitionSequence

namespace Lax228581.TwinWidth

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

end Lax228581.TwinWidth
end
