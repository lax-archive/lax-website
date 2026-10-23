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

namespace Grassmannian

/-- The unit sphere `𝕊_V = {x ∈ V : ‖x‖ = 1}`. -/
def sphere (V : Grassmannian X) : Set X :=
  Metric.sphere (0 : X) 1 ∩ (V.1 : Set X)

/-- `V ↦ 𝕊_V`, as a closed subset of `X`. -/
def toCloseds (V : Grassmannian X) : Closeds X :=
  ⟨V.sphere, Metric.isClosed_sphere.inter V.2.isClosed⟩

end Grassmannian

variable (X)

variable {X}

namespace GrassmannianFin

end GrassmannianFin

end Lax606786.BanachGrassmannian
end
