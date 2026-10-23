-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Closeds

-- Lax606786.BanachGrassmannian
section
namespace Lax606786
end Lax606786

namespace Lax606786.BanachGrassmannian
end Lax606786.BanachGrassmannian

namespace Lax606786.BanachGrassmannian.Grassmannian
end Lax606786.BanachGrassmannian.Grassmannian

namespace Lax606786.BanachGrassmannian.GrassmannianFin
end Lax606786.BanachGrassmannian.GrassmannianFin
end

-- Lax606786.OperatorStatistics
section
namespace Lax606786.OperatorStatistics
end Lax606786.OperatorStatistics
end

-- Lax606786.MeasurableOperatorFamilies
section
namespace Lax606786.MeasurableOperatorFamilies

open TopologicalSpace

open Lax606786.BanachGrassmannian Lax606786.OperatorStatistics

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strongly measurable family applied to a measurable vector field is measurable. -/
axiom measurable_apply {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [BorelSpace X] [SeparableSpace X] {A : Ω → X →L[ℝ] X}
    (hA : ∀ x : X, Measurable fun ω => A ω x) {v : Ω → X} (hv : Measurable v) :
    Measurable fun ω => A ω (v ω)

end Lax606786.MeasurableOperatorFamilies
end
