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
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency

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

end Lax323828.ManyTableConsistency
end
