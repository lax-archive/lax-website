-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency

open FiniteProbability

def LowDiversity {ι Ω X : Type} [Fintype ι] [DecidableEq X]
    (S : Ω → Finset X) (k : ℕ) (w : ι → Ω) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ (Finset.univ.image y).card ≤ k

end Lax253009.ManyTableConsistency
end
