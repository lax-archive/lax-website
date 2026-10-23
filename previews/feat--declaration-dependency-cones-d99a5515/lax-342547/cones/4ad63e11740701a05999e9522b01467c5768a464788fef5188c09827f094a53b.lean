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
namespace Lax342547.RawFrames

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

structure Frame (E : Matrix B B Binary) where
  P : Matrix N B Binary
  Q : Matrix N B Binary
  X : Matrix N H Binary
  Y : Matrix N H Binary
  plus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)
  minus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)
  gram : P.transpose * Q = E
  plus_annihilator : X.transpose * Q = 0
  minus_annihilator : P.transpose * Y = 0

variable {B H N}

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

def contraction {E : Matrix B B Binary} (F : Frame B H N E) :
    Matrix N N Binary →ₗ[Binary] Binary where
  toFun Z := Matrix.trace (F.X * F.Y.transpose * Z)
  map_add' Z W := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.trace_smul]

variable {Comp : Type}

def profileMap {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix B B Binary) →ₗ[Binary] (Comp → Matrix N N Binary) where
  toFun x e := sandwich (F e).P (F e).Q (x e)
  map_add' x y := by ext e i j; simp
  map_smul' c x := by ext e i j; simp

def profileContraction [Fintype Comp] {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix N N Binary) →ₗ[Binary] Binary :=
  ∑ e, (contraction (F e)).comp (LinearMap.proj e)

axiom tensor_realization {E : Matrix B B Binary} (F : Comp → Frame B H N E) [Fintype Comp] :
    Function.Injective (profileMap F) ∧
      ∀ x, profileContraction F (profileMap F x) = 0

end Lax342547.RawFrames
end
