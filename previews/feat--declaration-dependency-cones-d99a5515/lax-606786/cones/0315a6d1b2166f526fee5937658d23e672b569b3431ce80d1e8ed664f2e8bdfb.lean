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

end GrassmannianFin

end Lax606786.BanachGrassmannian
end
