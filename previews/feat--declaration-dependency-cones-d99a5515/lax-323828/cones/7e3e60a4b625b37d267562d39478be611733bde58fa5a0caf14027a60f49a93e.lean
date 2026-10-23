-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.ProductMoments
section
namespace Lax323828
end Lax323828

namespace Lax323828.ProductMoments
end Lax323828.ProductMoments
end

-- Lax323828.HigherMoments
section
namespace Lax323828.HigherMoments

open scoped BigOperators

axiom factorization {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {m : ℕ} (S : Fin m → Finset ι) (B : Fin m → κ → ℝ) :
  (𝔼 f : ι → κ, ∏ j, ∏ i ∈ S j, B j (f i)) =
    ∏ i, (𝔼 z, ∏ j with i ∈ S j, B j z)

end Lax323828.HigherMoments
end
