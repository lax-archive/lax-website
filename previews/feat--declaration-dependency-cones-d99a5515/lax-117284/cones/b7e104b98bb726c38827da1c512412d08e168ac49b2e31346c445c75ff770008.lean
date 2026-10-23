-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

-- Lax117284.BipartiteKuhn
section
namespace Lax117284.BipartiteKuhn.runAll
end Lax117284.BipartiteKuhn.runAll

namespace Lax117284.BipartiteKuhn.step
end Lax117284.BipartiteKuhn.step

namespace Lax117284.BipartiteKuhn.tryAugment
end Lax117284.BipartiteKuhn.tryAugment

namespace Lax117284.BipartiteKuhn

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- A matching respects the graph: every right vertex's match is one of its neighbours. -/
def Respects (adj : L → R → Prop) (μ : R → Option L) : Prop :=
  ∀ r l, μ r = some l → adj l r

end Lax117284.BipartiteKuhn
end
