-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax195003.WelzlOrders
section
namespace Lax195003.WelzlOrders

/-- A set system on `α`: a family of subsets of the ground set `α`. -/
abbrev SetSystem (α : Type*) := Set (Set α)

/-- The number of consecutive pairs in the order `π` with exactly one
endpoint in `X`. -/
noncomputable def crossingCount {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) : ℕ :=
  {u : Fin n | ∃ v : Fin n,
    (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}.ncard

/-- The crossing number of `π` with respect to `𝓕`: the largest crossing
count of a member of the set system. -/
noncomputable def crossingNumber {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) : ℕ :=
  sSup {k : ℕ | ∃ X ∈ 𝓕, k = crossingCount π X}

end Lax195003.WelzlOrders
end

-- Lax195003.WelzlOrdersNeighborhoodSetSystem
section
namespace Lax195003.WelzlOrdersNeighborhoodSetSystem

open Lax195003.WelzlOrders

/-- The neighborhood set system of a graph at radius `k`: the open
`k`-neighborhood of every vertex. -/
def neighborhoodSetSystem {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    SetSystem (Fin n) :=
  {X | ∃ v : Fin n, X =
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ k}}

end Lax195003.WelzlOrdersNeighborhoodSetSystem
end

-- Lax228581.TwinWidth
section
namespace Lax228581.TwinWidth

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

end Lax228581.TwinWidth
end

-- Lax214022.Cographs
section
namespace Lax214022.Cographs

open Lax228581.TwinWidth

/-- A finite graph is a cograph when it admits a contraction sequence of red
degree zero. -/
def IsCograph {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  HasTwinWidthAtMost G 0

end Lax214022.Cographs
end

-- Lax214022.CographWelzlLowerBound
section
namespace Lax214022.CographWelzlLowerBound

open Lax195003.WelzlOrders

open Lax195003.WelzlOrdersNeighborhoodSetSystem

open Lax214022.Cographs

/-- There are cographs of order at most `4^k` on which every Welzl order has
crossing number at least `k`. -/
axiom exists_cograph_requiring_crossingNumber_at_least (k : ℕ) :
    ∃ n : ℕ, 3 ^ k ≤ n ∧ n ≤ 4 ^ k ∧
      ∃ G : SimpleGraph (Fin n), IsCograph G ∧
        ∀ π : Equiv.Perm (Fin n),
          k ≤ crossingNumber (neighborhoodSetSystem G 1) π

end Lax214022.CographWelzlLowerBound
end
