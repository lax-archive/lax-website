-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.ProductMoments
section
namespace Lax253009.ProductMoments

open scoped BigOperators

noncomputable def weightedSum {ι κ : Type} (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ)) (f : ι → κ) : ℝ :=
  ∑ S ∈ supports, c S * ∑ B ∈ predicates, ∏ i ∈ S, B (f i)

axiom high_degree_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (supports : Finset (Finset ι))
    (c : Finset ι → ℝ) (predicates : Finset (κ → ℝ)) (l : ℕ)
    (hbalanced : ∀ B ∈ predicates, (𝔼 z, B z) = 0)
    (hbounded : ∀ B ∈ predicates, ∀ z, |B z| ≤ 1)
    (hdegree : ∀ S ∈ supports, l ≤ S.card)
    (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
  (𝔼 f : ι → κ, weightedSum supports c predicates f ^ 2) ≤
    ∑ B ∈ predicates, ∑ C ∈ predicates, |𝔼 z, B z * C z| ^ l

end Lax253009.ProductMoments
end
