-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.LeafTrimming
section
namespace Lax342547.LeafTrimming

open scoped ENNReal

axiom density_after_restriction {Ω : Type} (p μ : PMF Ω)
    (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (C ζ : ℝ) (N : ℕ)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (C * N) * μ o) :
    ∀ o, (p.filter S hS) o ≤ (2 : ℝ≥0∞) ^ ((C + ζ) * N) * μ o

end Lax342547.LeafTrimming
end
