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

end Lax606786.OperatorStatistics
end

-- Lax606786.GrowthUnderProjections
section
namespace Lax606786.GrowthUnderProjections

open Lax606786.BanachGrassmannian Lax606786.OperatorStatistics

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Compressing to a codimension-`k` subspace costs at most `k` Bernstein indices. -/
axiom bernsteinNumber_add_le_comp_proj (k l : ℕ) (hl : l ≠ 0) (V : GrassmannianCofin X k)
    (P : X →L[ℝ] X) (hP : ∀ x, P x ∈ (V.1.1 : Submodule ℝ X))
    (hidem : ∀ x ∈ (V.1.1 : Submodule ℝ X), P x = x) (T : X →L[ℝ] X) :
    bernsteinNumber T (k + l) ≤ bernsteinNumber (T.comp P) l

end Lax606786.GrowthUnderProjections
end
