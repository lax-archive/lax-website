-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax342547.DirectRanks
section
namespace Lax342547.DirectRanks
end Lax342547.DirectRanks
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

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits
end Lax342547.SpanDeficits
end

-- Lax342547.BlockDeficits
section
namespace Lax342547.BlockDeficits
end Lax342547.BlockDeficits
end

-- Lax342547.SumRank
section
namespace Lax342547.SumRank

open Lax342547.SpanDeficits

open scoped BigOperators

axiom sum_rank_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (hS : ∀ i, LinearMap.range (M i) ≤ S i) :
    (∑ i, Module.finrank K (LinearMap.range (M i))) ≤
      Module.finrank K (LinearMap.range (∑ i, M i))+
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W))+
      ((∑ i, Module.finrank K (LinearMap.range (M i).dualMap))-
        Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V)))

end Lax342547.SumRank
end
