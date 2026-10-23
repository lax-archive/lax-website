-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.BernoulliSampling
section
namespace Lax253009.BernoulliSampling

open FiniteProbability

noncomputable def count {Ω : Type} [Fintype Ω] (N : ℕ) (P : Ω → Prop)
    (z : Fin N → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i ↦ P (z i))).card

axiom upper_tail {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (N : ℕ) (P : Ω → Prop) (p : ℝ) (hp : 0 ≤ p) (hP : probability P ≤ p) :
    probability (fun z : Fin N → Ω ↦ 4 * N * p ≤ (count N P z : ℝ)) ≤
      Real.exp (-(N : ℝ) * p)

end Lax253009.BernoulliSampling
end
