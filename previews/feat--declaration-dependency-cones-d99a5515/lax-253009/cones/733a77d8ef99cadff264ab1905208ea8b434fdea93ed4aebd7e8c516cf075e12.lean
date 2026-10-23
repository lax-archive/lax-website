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

end Lax253009.FiniteProbability
end

-- Lax253009.MajorityAmplification
section
namespace Lax253009.MajorityAmplification

open FiniteProbability

def vote (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def errorMap (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

axiom majority_error {α : Type} [Fintype α] [Nonempty α]
    (answer : α → Bool) (b : Bool) :
    probability (fun r : α × α × α ↦
      vote (answer r.1) (answer r.2.1) (answer r.2.2) ≠ b) =
    errorMap (probability (fun r ↦ answer r ≠ b))

end Lax253009.MajorityAmplification
end
