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

axiom nested_weighted_filter {Ω : Type} (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS).toOuterMeasure T * ((p.filter S hS).filter T hT) o =
      (S ∩ T).indicator p o

end Lax342547.MixtureRecovery
end
