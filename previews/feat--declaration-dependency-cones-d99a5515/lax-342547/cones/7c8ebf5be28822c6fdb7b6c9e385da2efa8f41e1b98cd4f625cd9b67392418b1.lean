-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits
end Lax342547.SpanDeficits
end

-- Lax342547.GreedySpans
section
namespace Lax342547.GreedySpans
end Lax342547.GreedySpans

namespace Lax342547.GreedySpans.Greedy
end Lax342547.GreedySpans.Greedy
end

-- Lax342547.ProjectedSpans
section
namespace Lax342547.ProjectedSpans
end Lax342547.ProjectedSpans
end

-- Lax342547.QuotientRank
section
namespace Lax342547.QuotientRank
end Lax342547.QuotientRank
end

-- Lax342547.RankLoss
section
namespace Lax342547.RankLoss
end Lax342547.RankLoss
end

-- Lax342547.CoverProjection
section
namespace Lax342547.CoverProjection

open Lax342547.GreedySpans

open scoped BigOperators

noncomputable def projection {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    T.dualCoannihilator →ₗ[K] (W ⧸ S) := S.mkQ.comp (M.comp T.dualCoannihilator.subtype)

end Lax342547.CoverProjection
end

-- Lax342547.CoverAvoidance
section
namespace Lax342547.CoverAvoidance
end Lax342547.CoverAvoidance
end

-- Lax342547.QuotientFactorLifts
section
namespace Lax342547.QuotientFactorLifts
end Lax342547.QuotientFactorLifts
end

-- Lax342547.ProjectedOffsets
section
namespace Lax342547.ProjectedOffsets

axiom actual_common_projection_offsets {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) (M₁ M₂ : V →ₗ[K] W)
    (hS₁ : Disjoint (LinearMap.range M₁) S) (hT₁ : Disjoint (LinearMap.range M₁.dualMap) T)
    (hS₂ : Disjoint (LinearMap.range M₂) S) (hT₂ : Disjoint (LinearMap.range M₂.dualMap) T)
    (hcommon : Lax342547.CoverProjection.projection M₁ S T = Lax342547.CoverProjection.projection M₂ S T) :
    ∃ P₁ P₂ : LinearMap.range (Lax342547.CoverProjection.projection M₁ S T) →ₗ[K] W,
    ∃ Q₁ Q₂ : V →ₗ[K] LinearMap.range (Lax342547.CoverProjection.projection M₁ S T),
      P₁.comp Q₁ = M₁ ∧ P₂.comp Q₂ = M₂ ∧
      LinearMap.range (P₁-P₂) ≤ S ∧ LinearMap.range (Q₁-Q₂).dualMap ≤ T ∧
      Disjoint (LinearMap.range P₁) S ∧ Disjoint (LinearMap.range Q₂.dualMap) T ∧
      M₁-M₂ = (P₁-P₂).comp Q₂+P₁.comp (Q₁-Q₂) ∧
      Module.finrank K (LinearMap.range (P₁-P₂))+
        Module.finrank K (LinearMap.range (Q₁-Q₂).dualMap) ≤
        2*Module.finrank K (LinearMap.range (Lax342547.CoverProjection.projection M₁ S T))

end Lax342547.ProjectedOffsets
end
