-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547.Conditioning

open scoped ENNReal

axiom weighted_filter {Ω : Type} (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS) o = S.indicator p o

end Lax342547.Conditioning
end
