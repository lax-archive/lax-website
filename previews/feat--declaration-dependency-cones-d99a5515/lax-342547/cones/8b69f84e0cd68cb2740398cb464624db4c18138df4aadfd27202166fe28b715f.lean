-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Trace

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame

namespace Lax342547.RawFrames

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

variable {B H N}

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

variable {Comp : Type}

end Lax342547.RawFrames
end
