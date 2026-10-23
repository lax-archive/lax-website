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
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency

open FiniteProbability

def LowDiversity {ι Ω X : Type} [Fintype ι] [DecidableEq X]
    (S : Ω → Finset X) (k : ℕ) (w : ι → Ω) : Prop :=
  ∃ y : ι → X, (∀ i, y i ∈ S (w i)) ∧ (Finset.univ.image y).card ≤ k

axiom low_diversity_bound {ι Ω X : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (S : Ω → Finset X) (B k : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hB : ∀ w, (S w).card ≤ B)
    (hpoint : ∀ x, probability (fun w ↦ x ∈ S w) ≤ p)
    (hsmall : (Fintype.card ι : ℝ) * B * p ≤ 1) :
    probability (LowDiversity (ι := ι) S k) ≤
      (2 : ℝ) ^ Fintype.card ι * ((Fintype.card ι : ℝ) * B * p) ^ (Fintype.card ι - k)

end Lax253009.ManyTableConsistency
end
