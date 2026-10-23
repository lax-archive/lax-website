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

/-- The left vertex `l` holds some right vertex. -/
def Matched (μ : R → Option L) (l : L) : Prop := ∃ r, μ r = some l

end Lax117284.BipartiteKuhn
end
