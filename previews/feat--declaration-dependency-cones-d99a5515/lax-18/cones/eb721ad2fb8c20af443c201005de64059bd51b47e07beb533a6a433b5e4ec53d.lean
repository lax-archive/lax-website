-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

end Lax18.RegularPartitions
end
