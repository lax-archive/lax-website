-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

end Lax342547.Walsh
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh

open Lax342547.MomentSpace Lax342547.Walsh

axiom separate_phase_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ)
    (u : (I → Binary) → Binary) (v : (J → Binary) → Binary) (c : Binary)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |(∑ x, ∑ y, f x * g y * sign (dotProduct x (A.mulVec y) + u x + v y + c)) /
      ((2 : ℝ) ^ Fintype.card I * 2 ^ Fintype.card J)| ≤ 1 / Real.sqrt ((2 : ℝ) ^ A.rank)

end Lax342547.BilinearWalsh
end
