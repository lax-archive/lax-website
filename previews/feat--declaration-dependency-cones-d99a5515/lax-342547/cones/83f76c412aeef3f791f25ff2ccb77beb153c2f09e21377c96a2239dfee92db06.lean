-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.MixtureRecovery
section
namespace Lax342547.MixtureRecovery

open scoped ENNReal

axiom fiber_residual {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K)
    (R : K → Set Ω) (τ δ : ℝ≥0∞)
    (hr : ∀ k, τ ≤ p.toOuterMeasure {o | f o = k} →
      p.toOuterMeasure (R k) ≤ δ * p.toOuterMeasure {o | f o = k}) :
    p.toOuterMeasure ({o | p.toOuterMeasure {x | f x = f o} < τ} ∪
        {o | τ ≤ p.toOuterMeasure {x | f x = f o} ∧ o ∈ R (f o)}) ≤
      p.toOuterMeasure {o | p.toOuterMeasure {x | f x = f o} < τ} + δ

end Lax342547.MixtureRecovery
end
