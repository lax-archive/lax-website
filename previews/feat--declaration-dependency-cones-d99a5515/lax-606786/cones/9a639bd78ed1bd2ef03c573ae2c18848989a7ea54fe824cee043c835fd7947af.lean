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

open Lax606786.BanachGrassmannian

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `g(T, V) = inf {‖T x‖ : x ∈ V, ‖x‖ = 1}`. -/
noncomputable def growth (T : X →L[ℝ] Y) (V : Submodule ℝ X) : ℝ :=
  sInf ((fun x : X => ‖T x‖) '' (Metric.sphere (0 : X) 1 ∩ (V : Set X)))

end Lax606786.OperatorStatistics
end

-- Lax606786.MeasurableOperatorFamilies
section
namespace Lax606786.MeasurableOperatorFamilies

open TopologicalSpace

open Lax606786.BanachGrassmannian Lax606786.OperatorStatistics

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `ω ↦ g(A_ω, V)` is measurable for a fixed subspace `V ≠ 0`. -/
axiom measurable_growth {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SeparableSpace X] {A : Ω → X →L[ℝ] X}
    (hA : ∀ x : X, Measurable fun ω => A ω x) (V : Submodule ℝ X)
    (hV : (Metric.sphere (0 : X) 1 ∩ (V : Set X)).Nonempty) :
    Measurable fun ω => growth (A ω) V

end Lax606786.MeasurableOperatorFamilies
end
