-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
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

axiom projection_rank_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    Module.finrank K (LinearMap.range (projection M S T)) ≤ Module.finrank K (LinearMap.range M)

end Lax342547.CoverProjection
end
