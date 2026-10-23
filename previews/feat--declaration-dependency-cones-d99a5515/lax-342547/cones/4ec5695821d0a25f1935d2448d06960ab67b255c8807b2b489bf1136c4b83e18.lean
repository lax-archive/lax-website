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

axiom mixture_event {Ω J : Type} [Fintype Ω] [Fintype J]
    (p : J → PMF Ω) (q : PMF Ω) (w : J → ℝ≥0∞)
    (hq : ∀ o, q o = ∑ j, w j * p j o) (S : Set Ω) :
    q.toOuterMeasure S = ∑ j, w j * (p j).toOuterMeasure S

end Lax342547.MixtureRecovery
end
