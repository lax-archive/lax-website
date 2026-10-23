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

axiom filtered_marginal {Ω V : Type} [Fintype Ω] (p : PMF Ω) (μ : PMF V)
    (f : Ω → V) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (M : ℝ≥0∞) (hp : ∀ v, p.map f v ≤ M * μ v) :
    ∀ v, (p.filter S hS).map f v ≤ (M / p.toOuterMeasure S) * μ v

end Lax342547.LeafTrimming
end
