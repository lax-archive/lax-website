-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Closeds

-- Lax606786.BanachGrassmannian
section
namespace Lax606786.BanachGrassmannian

open TopologicalSpace

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `𝒢X`: the closed subspaces of `X` admitting a bounded projection onto them. -/
def Grassmannian : Type _ :=
  {V : Submodule ℝ X // V.ClosedComplemented}

variable {X}

namespace Grassmannian

end Grassmannian

variable (X)

/-- `𝒢^k X`: the subspaces in `𝒢X` of codimension `k`. -/
def GrassmannianCofin (k : ℕ) : Type _ :=
  {V : Grassmannian X // FiniteDimensional ℝ (X ⧸ (V.1 : Submodule ℝ X)) ∧
    Module.finrank ℝ (X ⧸ (V.1 : Submodule ℝ X)) = k}

/-- `𝒢_k X`: the `k`-dimensional subspaces of `X`. -/
def GrassmannianFin (k : ℕ) : Type _ :=
  {V : Submodule ℝ X // FiniteDimensional ℝ V ∧ Module.finrank ℝ V = k}

variable {X}

namespace GrassmannianFin

end GrassmannianFin

end Lax606786.BanachGrassmannian
end

-- Lax606786.ExtendedLog
section
namespace Lax606786.ExtendedLog

/-- `log r` for `r > 0`, and `-∞` for `r ≤ 0`. -/
noncomputable def logEReal (r : ℝ) : EReal := if r ≤ 0 then ⊥ else (Real.log r : EReal)

end Lax606786.ExtendedLog
end

-- Lax606786.OperatorStatistics
section
namespace Lax606786.OperatorStatistics

open Lax606786.BanachGrassmannian

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `g(T, V) = inf {‖T x‖ : x ∈ V, ‖x‖ = 1}`. -/
noncomputable def growth (T : X →L[ℝ] Y) (V : Submodule ℝ X) : ℝ :=
  sInf ((fun x : X => ‖T x‖) '' (Metric.sphere (0 : X) 1 ∩ (V : Set X)))

/-- `ρ_k(T) = sup {g(T, V) : V ∈ 𝒢_k X}`. -/
noncomputable def bernsteinNumber (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sSup (Set.range fun V : GrassmannianFin X k => growth T (V.1 : Submodule ℝ X))

end Lax606786.OperatorStatistics
end

-- Lax606786.TemperedFunctions
section
namespace Lax606786.TemperedFunctions

open MeasureTheory Filter Topology

/-- `f(σⁿω)/n → 0` for `μ`-a.e. `ω`. -/
def Tempered {Ω : Type*} [MeasurableSpace Ω] (σ : Ω → Ω) (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (σ^[n] ω) / n) atTop (𝓝 0)

end Lax606786.TemperedFunctions
end

-- Lax606786.Cocycles
section
namespace Lax606786.Cocycles.Cocycle.lambdaIdx
end Lax606786.Cocycles.Cocycle.lambdaIdx

namespace Lax606786.Cocycles

open MeasureTheory Filter

open Lax606786.OperatorStatistics Lax606786.ExtendedLog Lax606786.TemperedFunctions

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- A strongly measurable, forward-integrable cocycle of bounded operators on `X` over an
invertible ergodic transformation of a Lebesgue probability space. -/
structure Cocycle (Ω X : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] where
  /-- The base transformation, a measurable bijection with measurable inverse. -/
  σ : Ω ≃ᵐ Ω
  /-- The invariant measure. -/
  μ : Measure Ω
  /-- The generator `ω ↦ 𝓛_ω`. -/
  L : Ω → X →L[ℝ] X
  isProbability : IsProbabilityMeasure μ
  nullSingleton : NullSingletonClass μ
  ergodic : Ergodic σ μ
  stronglyMeasurable : ∀ x : X, Measurable (fun ω => L ω x)
  forwardIntegrable : Integrable (fun ω => Real.log (max ‖L ω‖ 1)) μ

attribute [instance] Cocycle.isProbability Cocycle.nullSingleton

namespace Cocycle

/-- `𝓛^{(n)}_ω = 𝓛_{σ^{n-1}ω} ∘ ⋯ ∘ 𝓛_ω`. -/
noncomputable def iterate (R : Cocycle Ω X) : ℕ → Ω → X →L[ℝ] X
  | 0, _ => ContinuousLinearMap.id ℝ X
  | n + 1, ω => (R.L (R.σ^[n] ω)).comp (R.iterate n ω)

/-- `χ_k(ω) = limsup (1/n) log ρ_k(𝓛^{(n)}_ω)`. Meaningful for `k ≥ 1`; `χ_0 = -∞`. -/
noncomputable def chi (R : Cocycle Ω X) (k : ℕ) (ω : Ω) : EReal :=
  limsup (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal)) atTop

/-- `ω ↦ log ‖P_ω‖` is tempered. -/
abbrev IsTempered (R : Cocycle Ω X) (P : Ω → X →L[ℝ] X) : Prop :=
  Tempered R.σ R.μ (fun ω => Real.log ‖P ω‖)

end Cocycle

end Lax606786.Cocycles
end

-- Lax606786.ModifiedCocycles
section
namespace Lax606786.ModifiedCocycles

open MeasureTheory Filter TopologicalSpace

open Lax606786.Cocycles Lax606786.BanachGrassmannian Lax606786.OperatorStatistics

open Classical in
/-- The modified cocycle has the signature of `R` shifted by the codimension of `V`. -/
axiom chi_modify {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (R R' : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] {M : ℕ}
    (F : Ω → Submodule ℝ X) (V : Ω → GrassmannianCofin X M) (Q : Ω → X →L[ℝ] X)
    (hQm : ∀ x, Measurable fun ω => Q ω x) {A : Set Ω} (hA : MeasurableSet A)
    (hApos : R.μ A ≠ 0) {C : ℝ} (hC : ∀ ω ∈ A, ‖Q ω‖ ≤ C)
    (hσ : R'.σ = R.σ) (hμ : R'.μ = R.μ)
    (hL : ∀ ω, R'.L ω = if ω ∈ A then (R.L ω).comp (Q ω) else R.L ω)
    (hidem : ∀ᵐ ω ∂(R.μ), (Q ω).comp (Q ω) = Q ω)
    (hrange : ∀ᵐ ω ∂(R.μ), LinearMap.range (Q ω : X →ₗ[ℝ] X) = ((V ω).1.1 : Submodule ℝ X))
    (hker : ∀ᵐ ω ∂(R.μ), LinearMap.ker (Q ω : X →ₗ[ℝ] X) = F ω)
    (heq : ∀ᵐ ω ∂(R.μ), (Q (R.σ ω)).comp (R.L ω) = (R.L ω).comp (Q ω))
    (htemp : R.IsTempered Q)
    (hgap : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop,
      ‖(R.iterate n ω).comp (Q ω)‖ < growth (R.iterate n ω) (F ω)) :
    ∀ᵐ ω ∂(R.μ), ∀ k : ℕ, 1 ≤ k → R'.chi k ω = R.chi (M + k) ω

end Lax606786.ModifiedCocycles
end
