-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.Grassmannian
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

-- Lax606786.GrassmannianComparison
section
namespace Lax606786.GrassmannianComparison

open Module.Grassmannian Lax606786.BanachGrassmannian

/-- `𝒢^k X` is the set of closed points of the algebraic Grassmannian `G(k, X; ℝ)`, by a
bijection that keeps the underlying subspace. -/
axiom exists_equiv_closed (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (k : ℕ) :
    ∃ e : GrassmannianCofin X k ≃
        {N : G(k, X; ℝ) // IsClosed ((N : Submodule ℝ X) : Set X)},
      ∀ V : GrassmannianCofin X k, ((e V).1 : Submodule ℝ X) = V.1.1

end Lax606786.GrassmannianComparison
end
