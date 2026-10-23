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

/-- `ω ↦ ‖T_ω‖` is measurable for a strongly measurable family `T` on a separable space. -/
axiom measurable_opNorm {Ω X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [SeparableSpace X] {T : Ω → X →L[ℝ] Y} (hT : ∀ x, Measurable fun ω => T ω x) :
    Measurable fun ω => ‖T ω‖

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Lax606786.MeasurableOperatorFamilies
end
