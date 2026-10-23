-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.BernoulliSampling
section
namespace Lax323828.BernoulliSampling

open scoped Classical

open FiniteProbability

/-- Count how many of the sampled points satisfy the event `P`. -/
noncomputable def count {Ω : Type} [Fintype Ω] (N : ℕ) (P : Ω → Prop)
    (z : Fin N → Ω) : ℕ :=
  (Finset.univ.filter (fun i ↦ P (z i))).card

axiom uniform_upper_tail {Ω I : Type} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (N m : ℕ) (P : I → Ω → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hI : Fintype.card I ≤ 2 ^ m) (hP : ∀ i, probability (P i) ≤ p)
    (hN : (m : ℝ) + 2 ≤ N * p) :
    probability (fun z : Fin N → Ω ↦ ∃ i, 4 * N * p ≤ (count N (P i) z : ℝ)) ≤ 1 / 4

end Lax323828.BernoulliSampling
end
