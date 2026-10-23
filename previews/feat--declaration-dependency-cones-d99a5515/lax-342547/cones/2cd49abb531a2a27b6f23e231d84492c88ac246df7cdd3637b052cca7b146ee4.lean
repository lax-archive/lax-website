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

open Lax342547.MomentSpace

def baseMoment {Base : Type} (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  fun i j => baseEval z i * baseEval z j

def IsBaseMoment {Base : Type} (Z : Matrix (Option Base) (Option Base) Binary) : Prop :=
  (∀ i j, Z i j = Z j i) ∧ ∀ i, Z i i = Z none i

end Lax342547.BaseMoments
end

-- Lax342547.SelectedMoments
section
namespace Lax342547.SelectedMoments

open Lax342547.MomentSpace Lax342547.BaseMoments

def rayProjection {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  1 - Matrix.vecMulVec (baseEval z) (Pi.single none 1)

axiom moment_ray {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) (Z : Matrix (Option Base) (Option Base) Binary)
    (hZ : IsBaseMoment Z)
    (h : rayProjection z * Z * (rayProjection z).transpose = 0) :
    Z = Z none none • baseMoment z

end Lax342547.SelectedMoments
end
