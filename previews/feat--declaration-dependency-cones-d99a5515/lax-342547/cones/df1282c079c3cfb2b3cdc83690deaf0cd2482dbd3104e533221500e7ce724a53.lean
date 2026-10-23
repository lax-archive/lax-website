-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

end Lax342547.MomentSpace
end

-- Lax342547.BaseMoments
section
namespace Lax342547.BaseMoments
end Lax342547.BaseMoments
end

-- Lax342547.SelectedMoments
section
namespace Lax342547.SelectedMoments

open Lax342547.MomentSpace Lax342547.BaseMoments

def rayProjection {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  1 - Matrix.vecMulVec (baseEval z) (Pi.single none 1)

axiom projection_kernel {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) :
    LinearMap.ker (rayProjection z).mulVecLin =
      Submodule.span Binary {baseEval z}

end Lax342547.SelectedMoments
end
