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
end Lax342547.FrameSymmetry

namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change
end

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

noncomputable instance {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) : Fintype (Orbit N G) := by classical exact Subtype.fintype _

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

def restrictOrbit {B H I J N : Type} [Fintype B] [Fintype H]
    [Fintype I] [Fintype J] [Fintype N] (G : Matrix B H Binary)
    (C : Matrix B I Binary) (D : Matrix H J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (z : Orbit N G) : Orbit N (C.transpose*G*D) :=
  ⟨(z.val.1*C,z.val.2*D),by
    refine ⟨?_,?_,?_⟩
    · intro x y hh
      apply hC
      apply z.property.1
      simpa only [Matrix.mulVec_mulVec] using hh
    · intro x y hh
      apply hD
      apply z.property.2.1
      simpa only [Matrix.mulVec_mulVec] using hh
    · simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc z.val.1.transpose,z.property.2.2]⟩

axiom slice_uniform {B H I J N : Type} [Fintype B] [Fintype H]
    [Fintype I] [Fintype J] [Fintype N] [DecidableEq N]
    (G : Matrix B H Binary) [Nonempty (Orbit N G)]
    (C : Matrix B I Binary) (D : Matrix H J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose*G*D))] :
    (PMF.uniformOfFintype (Orbit N G)).map (restrictOrbit G C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose*G*D))

end

end Lax342547.OrbitSliceLaw
end
