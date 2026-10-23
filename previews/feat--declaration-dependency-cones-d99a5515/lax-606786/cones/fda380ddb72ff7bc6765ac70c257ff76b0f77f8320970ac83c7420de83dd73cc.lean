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

/-- The unit sphere `𝕊_V = {x ∈ V : ‖x‖ = 1}`. -/
def sphere {k : ℕ} (V : GrassmannianFin X k) : Set X :=
  Metric.sphere (0 : X) 1 ∩ (V.1 : Set X)

/-- `V` is the span of its unit sphere. -/
theorem span_sphere {k : ℕ} (V : GrassmannianFin X k) :
    Submodule.span ℝ V.sphere = (V.1 : Submodule ℝ X) := by
  apply le_antisymm
  · exact Submodule.span_le.2 Set.inter_subset_right
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    · have hxeq : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
      rw [hxeq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, V.1.smul_mem _ hx⟩)
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]

/-- `𝕊_V` is compact. -/
theorem isCompact_sphere {k : ℕ} (V : GrassmannianFin X k) : IsCompact V.sphere := by
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have himg : V.sphere =
      (Subtype.val : (V.1 : Submodule ℝ X) → X) '' Metric.sphere (0 : (V.1 : Submodule ℝ X)) 1 := by
    ext x
    simp only [sphere, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨hx1, hxV⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      rwa [mem_sphere_zero_iff_norm] at hx1 ⊢
    · rintro ⟨v, hv, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hv
      exact ⟨by rwa [mem_sphere_zero_iff_norm], v.2⟩
  rw [himg]
  exact (_root_.isCompact_sphere (0 : (V.1 : Submodule ℝ X)) 1).image continuous_subtype_val

/-- `𝕊_V` is nonempty when `k ≠ 0`. -/
theorem nonempty_sphere {k : ℕ} [NeZero k] (V : GrassmannianFin X k) : V.sphere.Nonempty := by
  have hne : (V.1 : Submodule ℝ X) ≠ ⊥ := by
    intro h
    apply NeZero.ne k
    have hfr := V.2.2
    rw [h, finrank_bot] at hfr
    exact hfr.symm
  obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖x‖⁻¹ • x, ?_, V.1.smul_mem _ hxV⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]

/-- `V ↦ 𝕊_V`, as a nonempty compact subset of `X`. -/
noncomputable def toNonemptyCompacts {k : ℕ} [NeZero k] (V : GrassmannianFin X k) :
    NonemptyCompacts X where
  carrier := V.sphere
  isCompact' := V.isCompact_sphere
  nonempty' := V.nonempty_sphere

/-- A subspace is the span of its unit sphere, so `V ↦ 𝕊_V` is injective. -/
theorem toNonemptyCompacts_injective (k : ℕ) [NeZero k] :
    Function.Injective (toNonemptyCompacts (X := X) (k := k)) := by
  intro V W h
  apply Subtype.ext
  rw [← V.span_sphere, ← W.span_sphere]
  exact congrArg (fun s : NonemptyCompacts X => Submodule.span ℝ (s : Set X)) h

/-- The metric on `𝒢_k X`: the Hausdorff distance between unit spheres. -/
noncomputable instance instMetricSpace (k : ℕ) [NeZero k] : MetricSpace (GrassmannianFin X k) :=
  MetricSpace.induced toNonemptyCompacts (toNonemptyCompacts_injective k) inferInstance

/-- The Borel `σ`-algebra of that metric. -/
noncomputable instance instMeasurableSpace (k : ℕ) [NeZero k] :
    MeasurableSpace (GrassmannianFin X k) :=
  borel (GrassmannianFin X k)

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

/-- `λ_ω(x) = limsup (1/n) log ‖𝓛^{(n)}_ω x‖`. -/
noncomputable def lambdaAt (R : Cocycle Ω X) (ω : Ω) (x : X) : EReal :=
  limsup (fun n : ℕ => logEReal ‖R.iterate n ω x‖ / (n : EReal)) atTop

/-- `χ_k(ω) = limsup (1/n) log ρ_k(𝓛^{(n)}_ω)`. Meaningful for `k ≥ 1`; `χ_0 = -∞`. -/
noncomputable def chi (R : Cocycle Ω X) (k : ℕ) (ω : Ω) : EReal :=
  limsup (fun n : ℕ => logEReal (bernsteinNumber (R.iterate n ω) k) / (n : EReal)) atTop

/-- The index `k` at which the distinct exponent `λ_i` first occurs among the `χ_k`: `1` for
`i = 1`, then the least `t ≥ 1` with `χ_t` below `λ_{i-1}`, and `0` once there is none. Index `0` is
not used. -/
noncomputable def lambdaIdx (R : Cocycle Ω X) : ℕ → Ω → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | (i + 2), ω => sInf {t : ℕ | 1 ≤ t ∧ R.chi t ω < R.chi (R.lambdaIdx (i + 1) ω) ω}

/-- The distinct exponent `λ_i` (for `i ≥ 1`). -/
noncomputable def lambda (R : Cocycle Ω X) (i : ℕ) (ω : Ω) : EReal :=
  R.chi (R.lambdaIdx i ω) ω

/-- The multiplicity `m_i` of `λ_i` (for `i ≥ 1`); `0` if there is no exponent `λ_i`. -/
noncomputable def mult (R : Cocycle Ω X) (i : ℕ) (ω : Ω) : ℕ :=
  R.lambdaIdx (i + 1) ω - R.lambdaIdx i ω

/-- The Bernstein index `ν(ω) = inf_{k ≥ 1} χ_k(ω)`. -/
noncomputable def nu (R : Cocycle Ω X) (ω : Ω) : EReal := ⨅ k : ℕ, R.chi (k + 1) ω

/-- `ν < λ₁` almost everywhere. -/
def IsQuasicompact (R : Cocycle Ω X) : Prop :=
  ∀ᵐ ω ∂(R.μ), R.nu ω < R.chi 1 ω

/-- `ω ↦ log ‖P_ω‖` is tempered. -/
abbrev IsTempered (R : Cocycle Ω X) (P : Ω → X →L[ℝ] X) : Prop :=
  Tempered R.σ R.μ (fun ω => Real.log ‖P ω‖)

end Cocycle

end Lax606786.Cocycles
end

-- Lax606786.OseledetsLevels
section
namespace Lax606786.OseledetsLevels

open MeasureTheory Filter Topology

open Lax606786.Cocycles Lax606786.BanachGrassmannian Lax606786.OperatorStatistics
  Lax606786.ExtendedLog

/-- The data of the decomposition after the fast spaces `E_1, …, E_l`: the newest fast space
`E = E_l` (of dimension `m`), their sum `F` (of dimension `M`), the slow space `V`, and the
projection `Q` onto `V` along `F`. -/
structure LevelData (Ω X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  M : ℕ
  m : ℕ+
  E : Ω → GrassmannianFin X m
  F : Ω → GrassmannianFin X M
  V : Ω → GrassmannianCofin X M
  Q : Ω → X →L[ℝ] X

/-- `D` is the decomposition after the fast spaces `E_1, …, E_l`, where `lam i` is the `i`-th
distinct exponent. -/
structure IsLevel {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (R : Cocycle Ω X) (lam : ℕ → EReal) (l : ℕ) (D : LevelData Ω X) : Prop where
  lambdaIdx_eq : ∀ᵐ ω ∂(R.μ), R.lambdaIdx (l + 1) ω = D.M + 1
  lam_real : ∃ r : ℝ, lam l = r
  lam_gap : lam (l + 1) < lam l
  Q_meas : ∀ x, Measurable fun ω => D.Q ω x
  Q_temp : R.IsTempered D.Q
  Q_idem : ∀ᵐ ω ∂(R.μ), (D.Q ω).comp (D.Q ω) = D.Q ω
  Q_range : ∀ᵐ ω ∂(R.μ),
    LinearMap.range (D.Q ω : X →ₗ[ℝ] X) = ((D.V ω).1.1 : Submodule ℝ X)
  Q_ker : ∀ᵐ ω ∂(R.μ), LinearMap.ker (D.Q ω : X →ₗ[ℝ] X) = ((D.F ω).1 : Submodule ℝ X)
  Q_equiv : ∀ᵐ ω ∂(R.μ), (D.Q (R.σ ω)).comp (R.L ω) = (R.L ω).comp (D.Q ω)
  E_meas : Measurable D.E
  E_equiv : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((D.E ω).1 : Submodule ℝ X)
    = ((D.E (R.σ ω)).1 : Submodule ℝ X)
  E_dim : ∀ᵐ ω ∂(R.μ), R.mult l ω = D.m
  E_norm : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
    ‖(R.iterate n ω).comp (((D.E ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal)) atTop
    (𝓝 (lam l))
  E_growth : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ => logEReal
    (growth (R.iterate n ω) ((D.E ω).1 : Submodule ℝ X)) / (n : EReal)) atTop (𝓝 (lam l))
  E_le_F : ∀ᵐ ω ∂(R.μ), ((D.E ω).1 : Submodule ℝ X) ≤ ((D.F ω).1 : Submodule ℝ X)
  F_growth : ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, (b : EReal) < lam l → ∀ᶠ n : ℕ in atTop,
    Real.exp (n * b) ≤ growth (R.iterate n ω) ((D.F ω).1 : Submodule ℝ X)
  slow_rate : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
    logEReal ‖(R.iterate n ω).comp (D.Q ω)‖ / (n : EReal)) atTop (𝓝 (lam (l + 1)))
  slow_char : ∀ᵐ ω ∂(R.μ),
    (((D.V ω).1.1 : Submodule ℝ X) : Set X) = {x : X | R.lambdaAt ω x ≤ lam (l + 1)}

end Lax606786.OseledetsLevels
end

-- Lax606786.LevelConstruction
section
namespace Lax606786.LevelConstruction

open MeasureTheory TopologicalSpace

open Lax606786.Cocycles Lax606786.OseledetsLevels

/-- The base level: the top fast space and its slow complement. -/
axiom exists_level_one {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    (hqc : R.IsQuasicompact) :
    ∃ D : LevelData Ω X, IsLevel R lam 1 D ∧
      ∀ᵐ ω ∂(R.μ), ((D.F ω).1 : Submodule ℝ X) = ((D.E ω).1 : Submodule ℝ X)

end Lax606786.LevelConstruction
end
