-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

-- Lax606786.SubadditiveFamilies
section
namespace Lax606786.SubadditiveFamilies

/-- `(f_n)` is a subadditive family of measurable functions over `σ`. -/
def IsSubadditiveFamily {Ω : Type*} [MeasurableSpace Ω] (σ : Ω → Ω) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω

end Lax606786.SubadditiveFamilies
end
