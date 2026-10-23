-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.QuotientRank
section
namespace Lax342547.QuotientRank
end Lax342547.QuotientRank
end

-- Lax342547.RankLoss
section
namespace Lax342547.RankLoss

axiom composition_rank_loss {K U V W X : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] X) (M : V →ₗ[K] W) (B : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.range (A.comp (M.comp B))) +
        Module.finrank K (LinearMap.ker A) +
        (Module.finrank K V-Module.finrank K (LinearMap.range B))

end Lax342547.RankLoss
end
