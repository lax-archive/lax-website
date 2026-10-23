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

axiom minentropy_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (ζ : ℝ) (N t : ℕ)
    (hζ : 0 ≤ ζ) (ht : 1 ≤ t)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : p.toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * N))) :
    (p.filter S hS).toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * t * N))

end Lax342547.LeafTrimming
end
