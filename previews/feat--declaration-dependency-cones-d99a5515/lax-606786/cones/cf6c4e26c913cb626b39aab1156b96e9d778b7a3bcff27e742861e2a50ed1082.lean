-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.EReal.Operations
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

-- Lax606786.WeaklySubadditiveCombinations
section
namespace Lax606786.WeaklySubadditiveCombinations

open MeasureTheory Filter Topology

/-- The forward, shifted and balanced averages of `f + t g` converge to `C_f + t C_g`. -/
axiom tendsto_add_smul {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ)
    (f g : ℕ → Ω → ℝ) (Kf Kg : ℝ)
    (hf : (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω + Kf)
    (hg : (∀ n, Measurable (g n)) ∧ ∀ m n ω, g (m + n) ω ≤ g m (σ^[n] ω) + g n ω + Kg)
    (hf1 : Integrable (fun ω => max (f 1 ω) 0) μ)
    (hg1 : Integrable (fun ω => max (g 1 ω) 0) μ)
    (t : ℝ) (Cf Cg : EReal) (hCf : Cf ≠ ⊤) (hCg : Cg ≠ ⊤)
    (hdef : Cf = ⊥ → Cg = ⊥ → 0 ≤ t)
    (hCfl : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n ω / n : EReal)) atTop (𝓝 Cf))
    (hCgl : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (g n ω / n : EReal)) atTop (𝓝 Cg)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((f n ω + t * g n ω) / n : EReal)) atTop
          (𝓝 (Cf + (t : EReal) * Cg)) ∧
      Tendsto (fun n : ℕ => ((f n (σ^[n] ω) + t * g n (σ^[n] ω)) / n : EReal)) atTop
          (𝓝 (Cf + (t : EReal) * Cg)) ∧
      Tendsto (fun n : ℕ =>
          ((f (2 * n) ((σ.symm : Ω → Ω)^[n] ω) + t * g (2 * n) ((σ.symm : Ω → Ω)^[n] ω)) /
            (2 * n) : EReal))
          atTop (𝓝 (Cf + (t : EReal) * Cg))

end Lax606786.WeaklySubadditiveCombinations
end
