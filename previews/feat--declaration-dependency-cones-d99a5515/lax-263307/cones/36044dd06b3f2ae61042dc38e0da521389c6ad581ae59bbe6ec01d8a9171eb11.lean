-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax263307.Entropy
section
namespace Lax263307.Entropy

/-- A nonnegative vector with total mass one. -/
def IsProbability {n : ℕ} (π : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ π v) ∧ (∑ v, π v) = 1

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

end Lax263307.Entropy
end

-- Lax263307.EntropyGap
section
namespace Lax263307.EntropyGap

open Entropy

/-- The expected loss in entropy dominates the ordered adjacency mass. -/
axiom average_entropy_gap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (probability : IsProbability π) (nonnegative : ∀ u v, 0 ≤ q u v)
    (symmetric : ∀ u v, q u v = q v u)
    (marginals : ∀ v, (∑ u, q u v) = π v)
    (edge_zero : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ entropy π - ∑ v, π v * entropy (fun u => q u v / π v)

end Lax263307.EntropyGap
end
