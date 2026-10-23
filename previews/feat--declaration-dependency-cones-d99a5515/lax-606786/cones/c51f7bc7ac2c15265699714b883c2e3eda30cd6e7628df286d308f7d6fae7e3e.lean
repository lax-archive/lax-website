-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.EReal.Operations
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

-- Lax606786.LowerIntegrals
section
namespace Lax606786
end Lax606786

namespace Lax606786.LowerIntegrals
end Lax606786.LowerIntegrals
end

-- Lax606786.SubadditiveFamilies
section
namespace Lax606786.SubadditiveFamilies

/-- `(f_n)` is a subadditive family of measurable functions over `σ`. -/
def IsSubadditiveFamily {Ω : Type*} [MeasurableSpace Ω] (σ : Ω → Ω) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω

end Lax606786.SubadditiveFamilies
end

-- Lax606786.BalancedKingman
section
namespace Lax606786.BalancedKingman

open MeasureTheory Filter Topology

open Lax606786.SubadditiveFamilies

/-- The forward, shifted and balanced averages all converge to the same constant. -/
axiom three_limits {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {σ : Ω ≃ᵐ Ω} (hσ : Ergodic (⇑σ) μ)
    {f : ℕ → Ω → ℝ} (hf : IsSubadditiveFamily (⇑σ) f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) (C : EReal)
    (hC : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n ω / n : EReal)) atTop (𝓝 C)) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n (σ^[n] ω) / n : EReal)) atTop (𝓝 C)) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        (f (2 * n) ((σ.symm : Ω → Ω)^[n] ω) / (2 * n) : EReal)) atTop (𝓝 C))

end Lax606786.BalancedKingman
end
