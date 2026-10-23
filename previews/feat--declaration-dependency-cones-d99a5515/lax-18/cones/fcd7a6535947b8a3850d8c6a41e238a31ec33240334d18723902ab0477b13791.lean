-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

-- Lax18.FiniteGraphPartitions
section
namespace Lax18.FiniteGraphPartitions

universe u

/-- An indexed partition of a finite vertex set. -/
structure VertexPartition (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The number of parts. -/
  partCount : ℕ
  /-- The part indexed by `i`. -/
  part : Fin partCount → Finset V
  /-- Every part is nonempty. -/
  nonempty_part : ∀ i : Fin partCount, (part i).Nonempty
  /-- Distinct parts are disjoint. -/
  pairwise_disjoint :
    ∀ i j : Fin partCount, i ≠ j → Disjoint (part i) (part j)
  /-- The parts cover all vertices. -/
  covers : ∀ v : V, ∃ i : Fin partCount, v ∈ part i

namespace VertexPartition

variable {V : Type u} [Fintype V] [DecidableEq V]

end VertexPartition

end Lax18.FiniteGraphPartitions
end
