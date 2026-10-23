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
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting

open Lax342547.MomentSpace

open scoped ENNReal

axiom card_low_rank {I J : Type} [Fintype I] [Fintype J] (r : ℕ) :
    Nat.card {M : Matrix I J Binary // M.rank ≤ r} ≤ 2 ^ ((Fintype.card I + Fintype.card J) * r)

end Lax342547.LowRankCounting
end
