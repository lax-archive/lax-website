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

axiom lift_quotient_factor {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (C : U →ₗ[K] (W ⧸ S)) (M : V →ₗ[K] W) (R : T.dualCoannihilator →ₗ[K] U)
    (hC : Function.Injective C) (hR : Function.Surjective R)
    (hS : Disjoint (LinearMap.range M) S) (hT : Disjoint (LinearMap.range M.dualMap) T)
    (hfactor : Lax342547.CoverProjection.projection M S T = C.comp R) :
    ∃ P : U →ₗ[K] W, ∃ Q : V →ₗ[K] U,
      P.comp Q = M ∧ S.mkQ.comp P = C ∧ Q.comp T.dualCoannihilator.subtype = R

end Lax342547.QuotientFactorLifts
end
