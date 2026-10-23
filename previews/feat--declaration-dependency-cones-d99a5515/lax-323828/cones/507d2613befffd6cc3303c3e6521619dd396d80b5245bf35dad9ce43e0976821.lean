-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.ProductMoments
section
namespace Lax323828.ProductMoments

open scoped BigOperators

axiom mixed_moment {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (B C : κ → ℝ)
    (hB : (𝔼 z, B z) = 0) (hC : (𝔼 z, C z) = 0) (S T : Finset ι) :
  (𝔼 f : ι → κ, (∏ i ∈ S, B (f i)) * (∏ i ∈ T, C (f i))) =
    if S = T then (𝔼 z, B z * C z) ^ S.card else 0

end Lax323828.ProductMoments
end
