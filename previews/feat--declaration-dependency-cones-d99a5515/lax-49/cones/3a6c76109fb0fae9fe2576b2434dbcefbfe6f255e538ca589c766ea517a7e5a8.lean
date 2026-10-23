-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax48.TwinWidth
section
namespace Lax48.TwinWidth

/-- Two vertex sets are homogeneous in `G`: either every pair of vertices
across them is adjacent, or none is. -/
def Homogeneous {V : Type} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)

/-- The red degree of a part `A` in a family of parts `P`: the number of
other parts of `P` that are not homogeneous with `A`. -/
noncomputable def redDegree {V : Type} (G : SimpleGraph V)
    (P : Finset (Finset V)) (A : Finset V) : ℕ :=
  {B | B ∈ P ∧ B ≠ A ∧ ¬ Homogeneous G A B}.ncard

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

/-- A partition sequence of `G` in which every part has red degree at most
`d`: starting from the singleton partition, each step merges two parts into
one, until a single part remains. -/
structure PartitionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of merge steps. -/
  stepCount : ℕ
  /-- The partition after each number of merge steps. -/
  partition : ℕ → Finset (Finset V)
  /-- The sequence starts at the singleton partition. -/
  starts : partition 0 = singletonPartition V
  /-- The sequence ends with a single part. -/
  ends : (partition stepCount).card ≤ 1
  /-- Each step merges two distinct parts into one and keeps all other
  parts. -/
  step_merges :
    ∀ i, i < stepCount → ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = insert (A ∪ B) (((partition i).erase A).erase B)
  /-- Every part of every partition in the sequence has red degree at most
  `d`. -/
  redDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ partition i →
      redDegree G (partition i) A ≤ d

/-- `G` has a partition sequence in which every part has red degree at most
`d`. -/
def HasTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (PartitionSequence G d)

/-- The twin-width of a finite simple graph: the least `d` such that the
graph has a partition sequence in which every part has red degree at most
`d`. -/
noncomputable def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {d | HasTwinWidthAtMost G d}

end Lax48.TwinWidth
end

-- Lax49.MixedMinorNumber
section
namespace Lax49.MixedMinorNumber

/-- A division of `Fin n` into `k` nonempty consecutive intervals in
increasing order. Disjointness and convexity of the parts follow from
`part_ordered` and `part_cover`. -/
structure Division (n k : ℕ) where
  /-- The `i`-th part of the division. -/
  part : Fin k → Finset (Fin n)
  /-- Every part is nonempty. -/
  part_nonempty : ∀ i, (part i).Nonempty
  /-- The parts cover the whole interval. -/
  part_cover : ∀ x : Fin n, ∃ i, x ∈ part i
  /-- Earlier-indexed parts lie strictly before later-indexed parts. -/
  part_ordered :
    ∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ part i → b ∈ part j → a < b

/-- A matrix cell is vertical when each column is constant within the row
part. -/
def cellVertical {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄, r₁ ∈ R.part i → r₂ ∈ R.part i →
    ∀ ⦃c : Fin m⦄, c ∈ C.part j → (M r₁ c ↔ M r₂ c)

/-- A matrix cell is horizontal when each row is constant within the column
part. -/
def cellHorizontal {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ R.part i →
    ∀ ⦃c₁ c₂ : Fin m⦄, c₁ ∈ C.part j → c₂ ∈ C.part j →
      (M r c₁ ↔ M r c₂)

/-- A matrix cell is mixed when it is neither vertical nor horizontal. -/
def cellMixed {n m k : ℕ} (M : Fin n → Fin m → Prop)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ cellVertical M R C i j ∧ ¬ cellHorizontal M R C i j

/-- A matrix has a `k`-mixed minor if suitable row and column `k`-divisions
make every induced cell mixed. -/
def HasMixedMinor {n m : ℕ} (M : Fin n → Fin m → Prop) (k : ℕ) : Prop :=
  ∃ R : Division n k, ∃ C : Division m k, ∀ i j : Fin k, cellMixed M R C i j

/-- The largest order of a mixed minor of a matrix. -/
noncomputable def matrixMixedNumber {n m : ℕ}
    (M : Fin n → Fin m → Prop) : ℕ :=
  sSup {k | HasMixedMinor M k}

/-- The adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type} {n : ℕ}
    (G : SimpleGraph V) (e : Fin n ≃ V) : Fin n → Fin n → Prop :=
  fun i j => G.Adj (e i) (e j)

/-- The mixed minor number of a finite simple graph: the least mixed number
of its adjacency matrix over all vertex orderings. -/
noncomputable def mixedMinorNumber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf (Set.range fun e : Fin (Fintype.card V) ≃ V =>
    matrixMixedNumber (orderedAdjacency G e))

end Lax49.MixedMinorNumber
end

-- Lax49.MixedMinorNumberFromTwinWidth
section
namespace Lax49.MixedMinorNumberFromTwinWidth

/-- Mixed minor number is bounded by a numerical function of twin-width. -/
axiom exists_mixedMinorNumber_bound_of_twinWidth :
    ∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Lax49.MixedMinorNumber.mixedMinorNumber G ≤ g (Lax48.TwinWidth.twinWidth G)

end Lax49.MixedMinorNumberFromTwinWidth
end
