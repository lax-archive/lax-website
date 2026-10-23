-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

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

/-- The size of a part of a vertex partition. -/
def partSize (P : VertexPartition V) (i : Fin P.partCount) : ℕ :=
  (P.part i).card

end VertexPartition

end Lax18.FiniteGraphPartitions
end

-- Lax18.EdgeDensity
section
namespace Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The number of adjacent ordered pairs from `A` to `B`. -/
noncomputable def edgeCountBetween (G : SimpleGraph V)
    (A B : Finset V) : ℕ := by
  classical
  exact ((A.product B).filter fun p : V × V => G.Adj p.1 p.2).card

/-- The real-valued edge density between two vertex sets. -/
noncomputable def density (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  if A.card = 0 ∨ B.card = 0 then
    0
  else
    (edgeCountBetween G A B : ℝ) / ((A.card : ℝ) * (B.card : ℝ))

end Lax18.EdgeDensity
end

-- Lax18.RegularPairs
section
namespace Lax18.RegularPairs
end Lax18.RegularPairs
end

-- Lax18.RegularPartitions
section
namespace Lax18.RegularPartitions
end Lax18.RegularPartitions
end

-- Lax18.PartitionEnergy
section
namespace Lax18.PartitionEnergy

open Lax18.EdgeDensity

open Lax18.FiniteGraphPartitions

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `Q.Refines P` means that every class of `Q` lies in a class of `P`. -/
def Refines (Q P : VertexPartition V) : Prop :=
  ∀ j : Fin Q.partCount,
    ∃ i : Fin P.partCount, Q.part j ⊆ P.part i

/-- The normalized weight of the ordered pair of classes `(i,j)`. -/
noncomputable def pairWeight (P : VertexPartition V)
    (i j : Fin P.partCount) : ℝ :=
  ((P.partSize i : ℝ) * (P.partSize j : ℝ)) /
    (Fintype.card V : ℝ) ^ 2

/-- The weighted mean-square density (or index) of a graph partition. -/
noncomputable def partitionEnergy (G : SimpleGraph V)
    (P : VertexPartition V) : ℝ :=
  ∑ i : Fin P.partCount,
    ∑ j : Fin P.partCount,
      pairWeight P i j * (density G (P.part i) (P.part j)) ^ 2

end Lax18.PartitionEnergy
end

-- Lax18.PartitionEnergyMonotonicity
section
namespace Lax18.PartitionEnergyMonotonicity

open Lax18.FiniteGraphPartitions

open Lax18.PartitionEnergy

universe u

/-- Refining a partition cannot decrease its energy. -/
axiom partitionEnergy_mono_of_refines :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P Q : VertexPartition V),
      Refines Q P → partitionEnergy G P ≤ partitionEnergy G Q

end Lax18.PartitionEnergyMonotonicity
end
