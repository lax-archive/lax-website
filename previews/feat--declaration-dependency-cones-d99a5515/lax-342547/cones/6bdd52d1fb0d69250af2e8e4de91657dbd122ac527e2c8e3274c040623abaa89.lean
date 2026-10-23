-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.Conditioning
section
namespace Lax342547.Conditioning

open scoped ENNReal

axiom filter_event {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) :
    (p.filter S hS).toOuterMeasure T = p.toOuterMeasure (S ∩ T) / p.toOuterMeasure S

end Lax342547.Conditioning
end
