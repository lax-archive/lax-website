-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

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

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling

open Entropy (adjacencyMass edgeCost)

/-- Finite outcome probabilities and their associated vertex sets. -/
structure Distribution (n q : ℕ) where
  /-- Probability of each outcome. -/
  probability : Fin q → ℝ
  /-- Probabilities are nonnegative. -/
  nonnegative : ∀ i, 0 ≤ probability i
  /-- Total probability is one. -/
  normalized : (∑ i, probability i) = 1
  /-- The vertices used by each outcome. -/
  vertices : Fin q → Finset (Fin n)

/-- Probability of using a particular vertex. -/
noncomputable def load {n q : ℕ} (P : Distribution n q) (v : Fin n) : ℝ :=
  ∑ i, if v ∈ P.vertices i then P.probability i else 0

/-- Expected number of used vertices. -/
noncomputable def expectedSize {n q : ℕ} (P : Distribution n q) : ℝ :=
  ∑ i, P.probability i * ((P.vertices i).card : ℝ)

/-- Sum of vertex-use probabilities equals expected size. -/
axiom expected_size_identity {n q : ℕ} (P : Distribution n q) :
  expectedSize P = ∑ v, load P v

end Lax263307.PathSampling
end
