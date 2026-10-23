-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency

open FiniteProbability

def Agreement {ι Ω X : Type} (S : Ω → Finset X) (q : ℕ)
    (w : ι → Ω) (g : Fin q → X → Bool) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ ∀ j, ∃ b, ∀ i, g j (y i) = b

end Lax323828.ManyTableConsistency
end
