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

axiom lifted_row_avoids_cover {K U V : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (T : Submodule K (Module.Dual K V)) (R : T.dualCoannihilator →ₗ[K] U)
    (Q : V →ₗ[K] U) (hR : Function.Surjective R)
    (hQ : Q.comp T.dualCoannihilator.subtype = R) :
    Disjoint (LinearMap.range Q.dualMap) T

end Lax342547.QuotientFactorLifts
end
