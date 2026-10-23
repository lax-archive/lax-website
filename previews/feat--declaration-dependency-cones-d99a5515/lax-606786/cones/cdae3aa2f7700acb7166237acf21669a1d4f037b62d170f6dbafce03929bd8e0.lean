-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Closeds

-- Lax606786.BanachGrassmannian
section
namespace Lax606786.BanachGrassmannian

open TopologicalSpace

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

namespace Grassmannian

end Grassmannian

variable (X)

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

instance instBorelSpace (k : ℕ) [NeZero k] : BorelSpace (GrassmannianFin X k) := ⟨rfl⟩

end GrassmannianFin

end Lax606786.BanachGrassmannian
end
