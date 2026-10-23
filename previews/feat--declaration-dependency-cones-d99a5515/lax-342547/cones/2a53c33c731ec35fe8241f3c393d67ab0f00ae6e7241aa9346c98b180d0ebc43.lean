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
end Lax342547.RetainedImages
end

-- Lax342547.CollisionExponents
section
namespace Lax342547.CollisionExponents

axiom pruning_overlap_bound (keyCount cellCount k Cn N : ℝ)
    (_hkey0 : 0 ≤ keyCount) (hcell0 : 0 ≤ cellCount)
    (hkey : keyCount ≤ (2 : ℝ)^(k*N)) (hcell : cellCount ≤ (2 : ℝ)^Cn)
    (hscale : 1+Cn ≤ N/200) :
    2 * keyCount * cellCount * (2 : ℝ)^(-(k+1/100)*N) ≤ (2 : ℝ)^(-N/200)

end Lax342547.CollisionExponents
end
