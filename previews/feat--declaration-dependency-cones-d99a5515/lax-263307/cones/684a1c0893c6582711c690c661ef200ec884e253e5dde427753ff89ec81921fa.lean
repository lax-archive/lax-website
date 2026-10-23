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

end Lax263307.Entropy
end
