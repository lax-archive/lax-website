-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

axiom bounded_power_mean {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) (q : ℝ) (hq : 0 ≤ q) (l : ℕ) :
  (𝔼 x, X x ^ l) ≤ q ^ l + probability (fun x ↦ q < X x)

end Lax253009.FiniteProbability
end
