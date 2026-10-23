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

end GrassmannianFin

end Lax606786.BanachGrassmannian
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

-- Lax606786.VolumeGrowthComparison
section
namespace Lax606786.VolumeGrowthComparison

open Lax606786.OperatorStatistics

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `D_k` is comparable to `ρ_1 ⋯ ρ_k`, uniformly in the operator. -/
axiom volumeGrowth_comparable (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ T : X →L[ℝ] X,
      c * volumeGrowth T k ≤ ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) ∧
      ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) ≤ C * volumeGrowth T k

end Lax606786.VolumeGrowthComparison
end
