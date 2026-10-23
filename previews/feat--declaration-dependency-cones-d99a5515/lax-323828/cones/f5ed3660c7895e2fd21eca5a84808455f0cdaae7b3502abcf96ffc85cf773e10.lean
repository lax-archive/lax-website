-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

axiom even_moment_bound {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : Even m) :
  probability (fun x ↦ t ≤ X x) ≤ (𝔼 x, X x ^ m) / t ^ m

end Lax323828.FiniteProbability
end
