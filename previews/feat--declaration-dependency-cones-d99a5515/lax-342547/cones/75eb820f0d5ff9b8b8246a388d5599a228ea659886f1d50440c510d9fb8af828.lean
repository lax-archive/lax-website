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

def allowed (A : Set Base) (i : Coord × Option Base) : Prop :=
  match i.2 with
  | none => True
  | some b => b ∈ A

noncomputable def mask (A : Set Base) (i : Coord × Option Base) : Binary :=
  by classical exact if allowed A i then 1 else 0

noncomputable def project (A : Set Base) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary →ₗ[Binary]
      Matrix (Coord × Option Base) (Coord × Option Base) Binary where
  toFun w i j := mask A i * w i j * mask A j
  map_add' w v := by
    ext i j
    change mask A i * (w i j + v i j) * mask A j =
      mask A i * w i j * mask A j + mask A i * v i j * mask A j
    simp [mul_add, add_mul]
  map_smul' c w := by
    ext i j
    change mask A i * (c * w i j) * mask A j = c * (mask A i * w i j * mask A j)
    simp [mul_assoc, mul_left_comm]

end Lax342547.MomentSpace
end
