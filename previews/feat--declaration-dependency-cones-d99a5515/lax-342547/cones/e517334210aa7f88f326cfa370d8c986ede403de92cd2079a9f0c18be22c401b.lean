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

axiom matrix_sandwich_rank_loss {K I J P Q : Type} [Field K]
    [Fintype I] [Fintype J] [Fintype P] [Fintype Q]
    (A : Matrix P I K) (M : Matrix I J K) (B : Matrix Q J K) :
    M.rank ≤ (A*M*B.transpose).rank +
      Module.finrank K (LinearMap.ker A.mulVecLin) +
      Module.finrank K (LinearMap.ker B.mulVecLin)

end Lax342547.RankLoss
end
