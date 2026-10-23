-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The five families of linear constraints defining `R_r(G,k)`. -/
structure IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) : Prop where
  /-- The empty moment is normalized. -/
  normalized : value y ∅ = 1
  /-- Each moment lies in the unit interval. -/
  bounds : ∀ A, 0 ≤ y A ∧ y A ≤ 1
  /-- Adding a vertex cannot increase a moment. -/
  monotone : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∀ v, value y (insert v A) ≤ value y A
  /-- Nonindependent sets have zero moment. -/
  vanishes : ∀ A : Coordinate n r, ¬G.IsIndepSet (A.val : Set (Fin n)) → y A = 0
  /-- The cardinality constraint remains valid after conditioning. -/
  mass : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∑ v : Fin n, value y (insert v A) = (k : ℝ) * value y A

/-- Vertex costs after conditioning on inclusion of `A`. -/
noncomputable def conditioned {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (v : Fin n) : ℝ :=
  value y (insert v A) / value y A

end Lax263307.LinearRelaxation
end

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ConditioningDistribution
section
namespace Lax263307.ConditioningDistribution

open LinearRelaxation

/-- Normalize conditioned vertex costs to a probability vector. -/
noncomputable def marginal {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (k : ℕ) (v : Fin n) : ℝ :=
  conditioned y A v / k

/-- The joint distribution obtained from moments containing two extra vertices. -/
noncomputable def joint {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (k : ℕ) (u v : Fin n) : ℝ :=
  value y (insert u (insert v A)) / ((k : ℝ) ^ 2 * value y A)

/-- The probability and conditional-probability identities for the moment relaxation. -/
axiom distribution_identities {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) :
    (∀ v, 0 ≤ marginal y A k v) ∧
    (∑ v : Fin n, marginal y A k v) = 1 ∧
    (∀ u v, 0 ≤ joint y A k u v) ∧
    (∀ u v, joint y A k u v = joint y A k v u) ∧
    (∀ v, (∑ u : Fin n, joint y A k u v) = marginal y A k v) ∧
    (∀ u v, G.Adj u v → joint y A k u v = 0) ∧
    (∀ u v, 0 < marginal y A k v →
      marginal y (insert v A) k u = joint y A k u v / marginal y A k v)

end Lax263307.ConditioningDistribution
end
