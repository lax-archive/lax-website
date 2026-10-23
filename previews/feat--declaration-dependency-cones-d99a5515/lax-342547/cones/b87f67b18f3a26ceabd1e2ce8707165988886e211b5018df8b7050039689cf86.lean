-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

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

open Lax342547.MomentSpace

def baseMoment {Base : Type} (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  fun i j => baseEval z i * baseEval z j

def baseMomentSpace (Base : Type) : Submodule Binary (Matrix (Option Base) (Option Base) Binary) :=
  Submodule.span Binary (Set.range (baseMoment (Base := Base)))

end Lax342547.BaseMoments
end
