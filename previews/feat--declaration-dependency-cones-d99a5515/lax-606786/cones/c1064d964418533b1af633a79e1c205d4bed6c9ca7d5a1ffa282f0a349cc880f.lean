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

/-- `‖T‖_c = inf {‖T - K‖ : K compact}`. -/
noncomputable def compactSeminorm (T : X →L[ℝ] X) : ℝ :=
  sInf ((fun K : X →L[ℝ] X => ‖T - K‖) '' {K | IsCompactOperator K})

/-- `s_k(T) = inf {‖T|_V‖ : V ∈ 𝒢^{k-1} X}`. -/
noncomputable def gelfandNumber (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sInf (Set.range fun V : GrassmannianCofin X (k - 1) =>
    ‖T.comp (V.1.1 : Submodule ℝ X).subtypeL‖)

end Lax606786.OperatorStatistics
end

-- Lax606786.GelfandBernsteinComparison
section
namespace Lax606786.GelfandBernsteinComparison

open Lax606786.OperatorStatistics

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `‖T‖_c ≤ 2k s_k`. -/
axiom compactSeminorm_le_gelfandNumber (T : X →L[ℝ] X) {k : ℕ} (hk : 1 ≤ k) :
    compactSeminorm T ≤ 2 * (k : ℝ) * gelfandNumber T k

end Lax606786.GelfandBernsteinComparison
end
