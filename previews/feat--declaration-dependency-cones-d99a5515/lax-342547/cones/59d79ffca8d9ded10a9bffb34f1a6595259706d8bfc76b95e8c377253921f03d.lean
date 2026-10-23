-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages

open Lax342547.PushforwardWalsh

axiom paper_conditional_cap (ζ k t N : ℝ) (hζ : 0 ≤ ζ)
    (hζsmall : ζ ≤ 1 / 1000) (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) (hN : 0 ≤ N) :
    (2 : ℝ) ^ (-(1 - 2 * ζ) * (k + t) * N) /
        (2 : ℝ) ^ (-(k + 1 / 100) * N) ≤ (2 : ℝ) ^ (-(95 / 100 : ℝ) * t * N)

end Lax342547.RetainedImages
end
