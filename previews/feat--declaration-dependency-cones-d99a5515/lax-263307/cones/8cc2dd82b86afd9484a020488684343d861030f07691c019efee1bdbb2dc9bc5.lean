-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

/-- Copies are adjacent precisely when their original vertices are adjacent. -/
def graph {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Vertex copies) := G.comap fun v => v.1

/-- Vertices represented by at least one selected copy. -/
def project {n : ℕ} {copies : Fin n → ℕ} (K : Finset (Vertex copies)) : Finset (Fin n) :=
  K.image fun v => v.1

/-- The usual multiplicative cardinality guarantee on the blow-up graph. -/
def IsCardinalityApproximation {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (δ : ℚ) (K : Finset (Vertex copies)) : Prop :=
  (graph G copies).IsIndepSet (K : Set (Vertex copies)) ∧
    ∀ J : Finset (Vertex copies), (graph G copies).IsIndepSet (J : Set (Vertex copies)) →
      (1 - δ) * (J.card : ℚ) ≤ K.card

end Lax263307.IndependentBlowUp
end

-- Lax263307.BlowUpIndependentSets
section
namespace Lax263307.BlowUpIndependentSets
end Lax263307.BlowUpIndependentSets
end

-- Lax263307.WeightRounding
section
namespace Lax263307.WeightRounding

/-- The maximum of the vertex weights and zero. -/
def maximumWeight {n : ℕ} (w : Fin n → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image w)).max' (Finset.insert_nonempty _ _)

/-- The weight unit used by the reduction. -/
def scale {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℚ :=
  ε * maximumWeight w / (2 * n)

/-- Multiplicities at a specified positive weight unit. -/
def roundedCopies {n : ℕ} (w : Fin n → ℚ) (τ : ℚ) : Fin n → ℕ :=
  fun v => ⌊w v / τ⌋₊

/-- The multiplicities chosen for the requested accuracy. -/
def copies {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : Fin n → ℕ :=
  roundedCopies w (scale w ε)

end Lax263307.WeightRounding
end

-- Lax263307.RoundingBounds
section
namespace Lax263307.RoundingBounds
end Lax263307.RoundingBounds
end

-- Lax263307.WeightedProjection
section
namespace Lax263307.WeightedProjection

open WeightedIndependentSet WeightRounding IndependentBlowUp

/-- The two half-accuracy losses combine into the requested weighted guarantee. -/
axiom approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (nonnegative : ∀ v, 0 ≤ w v) (positive_order : 0 < n)
    (positive_accuracy : 0 < ε) (accuracy_lt_one : ε < 1)
    (positive_maximum : 0 < maximumWeight w)
    (K : Finset (Vertex (copies w ε)))
    (approximation : IsCardinalityApproximation G (copies w ε) (ε / 2) K) :
    IsApproximation G w ε (project K)

end Lax263307.WeightedProjection
end
