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

-- Lax342547.JoinedGramOrbits
section
namespace Lax342547.JoinedGramOrbits

open Lax342547.MomentSpace Lax342547.FrameTuples

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]

def joined {G : Matrix I J Binary} {H : Matrix K L Binary} (z : Orbit N G × Orbit N H) :=
  (Matrix.fromCols z.1.val.1 z.2.val.1,Matrix.fromCols z.1.val.2 z.2.val.2)

def Compatible (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    (z : Orbit N G × Orbit N H) : Prop :=
  Function.Injective (joined z).1.mulVec ∧ Function.Injective (joined z).2.mulVec ∧
    z.1.val.1.transpose*z.2.val.2 = A ∧ z.2.val.1.transpose*z.1.val.2 = B

axiom compatible_filter (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    [Nonempty (Orbit N (Matrix.fromBlocks G A B H))]
    [Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z}]
    (h : ∃ z ∈ {z : Orbit N G × Orbit N H | Compatible G H A B z},
      z ∈ (PMF.uniformOfFintype (Orbit N G × Orbit N H)).support) :
    ((PMF.uniformOfFintype (Orbit N G × Orbit N H)).filter
        {z | Compatible G H A B z} h).map joined =
      (PMF.uniformOfFintype (Orbit N (Matrix.fromBlocks G A B H))).map Subtype.val

end Lax342547.JoinedGramOrbits
end
