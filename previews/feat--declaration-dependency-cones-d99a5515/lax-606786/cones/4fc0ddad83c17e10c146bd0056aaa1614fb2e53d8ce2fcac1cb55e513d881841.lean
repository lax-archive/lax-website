-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
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

open Classical in
/-- `D_k(T)`: the supremum over unit `k`-tuples `u` of `∏ᵢ d(T uᵢ, span {T u_j : j < i})`. -/
noncomputable def volumeGrowth (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sSup (Set.range fun u : Fin k → X =>
    if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then
      ∏ i : Fin k, Metric.infDist (T (u i))
        ((Submodule.span ℝ ((fun j : Fin k => T (u j)) '' {j | j < i})) : Set X)
    else 0)

end Lax606786.OperatorStatistics
end
