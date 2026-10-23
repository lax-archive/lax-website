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

open Lax342547.SpanDeficits

open scoped BigOperators

axiom nonzero_map_rank {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (M : V →ₗ[K] W) (hM : M ≠ 0) :
    1 ≤ Module.finrank K (LinearMap.range M)

end Lax342547.BlockDeficits
end
