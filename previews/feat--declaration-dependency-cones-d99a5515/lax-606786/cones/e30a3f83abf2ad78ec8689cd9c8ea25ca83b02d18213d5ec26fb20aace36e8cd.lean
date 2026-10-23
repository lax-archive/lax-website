-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.EReal.Operations
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- Lax606786.LowerIntegrals
section
namespace Lax606786.LowerIntegrals

open MeasureTheory

/-- `L_μ(g) = inf_M ∫ max(g, -M) dμ`. -/
noncomputable def lowerIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) :
    EReal :=
  ⨅ M : ℕ, ((∫ ω, max (g ω) (-(M : ℝ)) ∂μ : ℝ) : EReal)

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

-- Lax606786.KingmanTheorem
section
namespace Lax606786.KingmanTheorem
end Lax606786.KingmanTheorem
end

-- Lax606786.KingmanVariants
section
namespace Lax606786.KingmanVariants

open MeasureTheory Filter Topology

open Lax606786.SubadditiveFamilies Lax606786.LowerIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Kingman's theorem along the shifted orbit, `f_n(σⁿω)/n → C`. -/
axiom kingman_shifted (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ)
    (f : ℕ → Ω → ℝ) (hf : IsSubadditiveFamily σ f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n (σ^[n] ω) / n : EReal)) atTop (𝓝 C)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (𝓝 C)

end Lax606786.KingmanVariants
end
