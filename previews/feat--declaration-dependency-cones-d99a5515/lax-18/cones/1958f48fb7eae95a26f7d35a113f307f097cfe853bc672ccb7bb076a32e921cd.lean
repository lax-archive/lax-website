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

/-- A partition is equitable if any two part sizes differ by at most one. -/
def Equitable (P : VertexPartition V) : Prop :=
  ∀ i j : Fin P.partCount,
    P.partSize i ≤ P.partSize j + 1 ∧
      P.partSize j ≤ P.partSize i + 1

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

open Lax18.EdgeDensity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `X` is a large enough subset of `A` for the threshold `ε`. -/
def LargeSubset (ε : ℝ) (A X : Finset V) : Prop :=
  X ⊆ A ∧ ε * (A.card : ℝ) ≤ (X.card : ℝ)

/-- The pair `(A,B)` is `ε`-regular in `G`. -/
def IsRegularPair (G : SimpleGraph V) (ε : ℝ) (A B : Finset V) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧
    ∀ X Y : Finset V,
      LargeSubset ε A X →
        LargeSubset ε B Y →
          |density G X Y - density G A B| ≤ ε

end Lax18.RegularPairs
end

-- Lax18.RegularPartitions
section
namespace Lax18.RegularPartitions

open Lax18.FiniteGraphPartitions

open Lax18.RegularPairs

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The unordered irregular pairs of parts, represented by index pairs
`i < j`. -/
noncomputable def irregularPairIndices
    (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : Finset (Fin P.partCount × Fin P.partCount) := by
  classical
  exact
    (Finset.univ.product Finset.univ).filter
      (fun p : Fin P.partCount × Fin P.partCount =>
        p.1 < p.2 ∧
          ¬ IsRegularPair G ε (P.part p.1) (P.part p.2))

/-- The number of unordered irregular pairs of parts. -/
noncomputable def irregularPairCount
    (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : ℕ :=
  (irregularPairIndices G ε P).card

/-- A partition is `ε`-regular if it has at most `ε k^2` irregular unordered
pairs of distinct parts. -/
def IsRegularPartition (G : SimpleGraph V) (ε : ℝ)
    (P : VertexPartition V) : Prop :=
  (irregularPairCount G ε P : ℝ) ≤ ε * (P.partCount : ℝ) ^ 2

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

-- Lax18.EnergyIncrement
section
namespace Lax18.EnergyIncrement

open Lax18.FiniteGraphPartitions

open Lax18.PartitionEnergy

open Lax18.RegularPartitions

universe u

/-- An irregular equitable partition admits a bounded refinement with a
definite energy increment. -/
axiom energy_increment_refinement :
  ∀ (ε : ℝ),
    0 < ε →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (P : VertexPartition V),
          P.Equitable →
            ¬ IsRegularPartition G ε P →
              ∃ Q : VertexPartition V,
                Refines Q P ∧
                  P.partCount ≤ Q.partCount ∧
                    Q.partCount ≤ P.partCount * 2 ^ P.partCount ∧
                      partitionEnergy G P + ε ^ 5 / 4 ≤
                        partitionEnergy G Q

end Lax18.EnergyIncrement
end
