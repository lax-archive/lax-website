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

/-- `𝒢X`: the closed subspaces of `X` admitting a bounded projection onto them. -/
def Grassmannian : Type _ :=
  {V : Submodule ℝ X // V.ClosedComplemented}

variable {X}

/-- Every subspace is spanned by its unit sphere. -/
theorem span_sphere_inter (V : Submodule ℝ X) :
    Submodule.span ℝ (Metric.sphere (0 : X) 1 ∩ (V : Set X)) = V := by
  apply le_antisymm
  · exact Submodule.span_le.2 Set.inter_subset_right
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    · have hxeq : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
      rw [hxeq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, V.smul_mem _ hx⟩)
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]

namespace Grassmannian

/-- The unit sphere `𝕊_V = {x ∈ V : ‖x‖ = 1}`. -/
def sphere (V : Grassmannian X) : Set X :=
  Metric.sphere (0 : X) 1 ∩ (V.1 : Set X)

/-- `V ↦ 𝕊_V`, as a closed subset of `X`. -/
def toCloseds (V : Grassmannian X) : Closeds X :=
  ⟨V.sphere, Metric.isClosed_sphere.inter V.2.isClosed⟩

/-- A subspace is the span of its unit sphere, so `V ↦ 𝕊_V` is injective. -/
theorem toCloseds_injective : Function.Injective (toCloseds (X := X)) := by
  intro V W h
  apply Subtype.ext
  rw [← span_sphere_inter V.1, ← span_sphere_inter W.1]
  exact congrArg (fun s : Closeds X => Submodule.span ℝ (s : Set X)) h

/-- The distance on `𝒢X`: the Hausdorff distance between unit spheres. -/
noncomputable instance instEMetricSpace : EMetricSpace (Grassmannian X) :=
  EMetricSpace.induced toCloseds toCloseds_injective inferInstance

end Grassmannian

variable (X)

variable {X}

namespace GrassmannianFin

end GrassmannianFin

end Lax606786.BanachGrassmannian
end
