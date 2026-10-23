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

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests
end Lax342547.FourierTests
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

-- Lax342547.GramTests
section
namespace Lax342547.GramTests

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.PushforwardWalsh

open Lax342547.FourierTests

axiom paper_walsh_factor (d : ℝ) :
    Real.sqrt ((2 : ℝ)^d * (2 : ℝ)^(-(95/100 : ℝ)*d) * (2 : ℝ)^(-(95/100 : ℝ)*d)) =
      (2 : ℝ)^(-(45/100 : ℝ)*d)

end Lax342547.GramTests
end
