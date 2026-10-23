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
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
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

end Lax342547.FrameSymmetry
end

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

end Lax342547.FrameTuples
end

-- Lax342547.OrbitSliceLaw
section
namespace Lax342547.OrbitSliceLaw

noncomputable section

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.FrameTuples

open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

def changeOrbit {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]
    (c : Change N) (G : Matrix B H Binary) (z : Orbit N G) : Orbit N G :=
  ⟨(c.C*z.val.1,c.D.transpose*z.val.2),by
    refine ⟨?_,?_,?_⟩
    · intro x y hh
      apply z.property.1
      apply c.injective
      simpa only [Matrix.mulVec_mulVec] using hh
    · intro x y hh
      apply z.property.2.1
      apply c.dual_injective
      simpa only [Matrix.mulVec_mulVec] using hh
    · have he : c.C.transpose*c.D.transpose = 1 := by simpa using congrArg Matrix.transpose c.DC
      simp only [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc c.C.transpose,
        he,Matrix.one_mul,z.property.2.2]⟩

end

end Lax342547.OrbitSliceLaw
end
