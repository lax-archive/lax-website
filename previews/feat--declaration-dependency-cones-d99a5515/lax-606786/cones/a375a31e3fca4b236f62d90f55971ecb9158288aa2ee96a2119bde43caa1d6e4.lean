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

end Grassmannian

variable (X)

/-- `𝒢_k X`: the `k`-dimensional subspaces of `X`. -/
def GrassmannianFin (k : ℕ) : Type _ :=
  {V : Submodule ℝ X // FiniteDimensional ℝ V ∧ Module.finrank ℝ V = k}

variable {X}

namespace GrassmannianFin

/-- A finite-dimensional subspace admits a bounded projection onto it, so `𝒢_k X` sits inside
`𝒢 X`. -/
theorem closedComplemented {k : ℕ} (V : GrassmannianFin X k) :
    (V.1 : Submodule ℝ X).ClosedComplemented := by
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  exact Submodule.ClosedComplemented.of_finiteDimensional _

/-- The inclusion `𝒢_k X → 𝒢 X`. -/
def toGrassmannian {k : ℕ} (V : GrassmannianFin X k) : Grassmannian X :=
  ⟨V.1, V.closedComplemented⟩

end GrassmannianFin

end Lax606786.BanachGrassmannian
end
