-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear

-- Lax342547.FlatRank
section
namespace Lax342547.FlatRank

axiom exists_flat_level (r : ℕ → ℕ) (A R J : ℕ) (hmono : Monotone r)
    (hbound : ∀ j ≤ J, r j ≤ R) (hroom : A + 2 * R + 2 ≤ J) :
    ∃ j, A ≤ j ∧ j + 2 ≤ J ∧ r j = r (j + 1) ∧ r (j + 1) = r (j + 2)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

end Lax342547.FlatRank
end
