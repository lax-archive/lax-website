-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Trace
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

variable {Comp : Type}

end Lax342547.RawFrames
end

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

structure Change (N : Type) [Fintype N] [DecidableEq N] where
  C : Matrix N N Binary
  D : Matrix N N Binary
  CD : C * D = 1
  DC : D * C = 1

theorem Change.injective (c : Change N) : Function.Injective c.C.mulVec := by
  intro x y h
  have h' := congrArg c.D.mulVec h
  simpa only [Matrix.mulVec_mulVec, c.DC, Matrix.one_mulVec] using h'

theorem Change.dual_injective (c : Change N) : Function.Injective c.D.transpose.mulVec := by
  have hDC : c.C.transpose * c.D.transpose = 1 := by
    simpa using congrArg Matrix.transpose c.DC
  intro x y h
  have h' := congrArg c.C.transpose.mulVec h
  simpa only [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec] using h'

def transform (c : Change N) {E : Matrix B B Binary} (F : Frame B H N E) :
    Frame B H N E where
  P := c.C * F.P
  Q := c.D.transpose * F.Q
  X := c.C * F.X
  Y := c.D.transpose * F.Y
  plus_injective := by
    intro x y h
    apply F.plus_injective
    apply c.injective
    simpa only [Matrix.mulVec_add, Matrix.mulVec_mulVec] using h
  minus_injective := by
    intro x y h
    apply F.minus_injective
    apply c.dual_injective
    simpa only [Matrix.mulVec_add, Matrix.mulVec_mulVec] using h
  gram := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.gram
  plus_annihilator := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.plus_annihilator
  minus_annihilator := by
    have hCD : c.C.transpose * c.D.transpose = 1 := by
      simpa using congrArg Matrix.transpose c.DC
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
      hCD, Matrix.one_mul] using F.minus_annihilator

end Lax342547.FrameSymmetry
end
