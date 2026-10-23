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

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

end Lax342547.Walsh
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def correlation {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  ∑ x, ∑ y, f x * g y * phase x (A.mulVec y)

noncomputable def average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  correlation A f g / (2 ^ Fintype.card I * 2 ^ Fintype.card J)

end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh

open Lax342547.MomentSpace

def bitMatrix {I J : Type} (C : Matrix I J Binary) (N : ℕ) :
    Matrix (Fin N × I) (Fin N × J) Binary :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

axiom nonzero_pattern_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (C : Matrix I J Binary) (hC : C ≠ 0) (N : ℕ)
    (f : (Fin N × I → Binary) → ℝ) (g : (Fin N × J → Binary) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |BilinearWalsh.average (bitMatrix C N) f g| ≤ 1 / Real.sqrt ((2 : ℝ) ^ N)

end Lax342547.SlotWalsh
end
