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

axiom event_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (τ b : ℝ≥0∞)
    (hτ : τ ≤ p.toOuterMeasure S) (hb : p.toOuterMeasure T ≤ b) :
    (p.filter S hS).toOuterMeasure T ≤ b / τ

end Lax342547.LeafTrimming
end
