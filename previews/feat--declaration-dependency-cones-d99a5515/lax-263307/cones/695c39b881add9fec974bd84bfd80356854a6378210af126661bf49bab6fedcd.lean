-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Log
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
end Lax263307.ConditioningDistribution
end

-- Lax263307.Entropy
section
namespace Lax263307.Entropy

/-- Entropy measured with natural logarithms. -/
noncomputable def naturalEntropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  ∑ v, Real.negMulLog (π v)

/-- Shannon entropy in bits. -/
noncomputable def entropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  naturalEntropy π / Real.log 2

/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end Lax263307.Entropy
end

-- Lax263307.EntropyBounds
section
namespace Lax263307.EntropyBounds
end Lax263307.EntropyBounds
end

-- Lax263307.EntropyGap
section
namespace Lax263307.EntropyGap
end Lax263307.EntropyGap
end

-- Lax263307.HeavyConditioning
section
namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * p * ((Nat.log2 n : ℝ) + 1))

axiom heavy_low_edge_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (order_positive : 0 < n) (target_positive : 0 < k)
    (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : (p : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ r) :
    ∃ A : Finset (Fin n), A.card ≤ r ∧ probabilityFloor n p ^ r ≤ value y A ∧
      0 < value y A ∧ (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
      (∑ v, conditioned y A v) = k ∧ edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p

end Lax263307.HeavyConditioning
end
