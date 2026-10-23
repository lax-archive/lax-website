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

axiom restriction_bound {α : Type} [Fintype α] (s : Finset α) (hs : s.Nonempty)
    (K : ℝ) (hcard : (Fintype.card α : ℝ) ≤ K * s.card) (P : α → Prop) :
  probability (fun x : s ↦ P x.val) ≤ K * probability P

end Lax253009.FiniteProbability
end
