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

-- Lax342547.CorankCounting
section
namespace Lax342547.CorankCounting

axiom exists_row_relations {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) (s : ℕ) (hs : M.rank + s ≤ Fintype.card I) :
    ∃ C : Matrix (Fin s) I K, Function.Surjective C.mulVec ∧ C * M = 0

open Lax342547.MomentSpace

open scoped ENNReal

end Lax342547.CorankCounting
end
