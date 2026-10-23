-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.Distributions.Uniform

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.SymmetricFactorization
section
namespace Lax342547.SymmetricFactorization

axiom symmetric_factorization {K I : Type} [Field K] [Fintype I]
    (M : Matrix I I K) (hM : M.transpose = M) :
    ∃ Z : Matrix I (Fin M.rank) K, ∃ H : Matrix (Fin M.rank) (Fin M.rank) K,
      Function.Injective Z.mulVec ∧ H.transpose = H ∧ Function.Bijective H.mulVec ∧
      Z * H * Z.transpose = M

open Lax342547.MomentSpace

end Lax342547.SymmetricFactorization
end
