-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.MomentRecovery
section
namespace Lax342547.MomentRecovery

open Lax342547.MomentSpace

def IsSelectorHankel {Base : Type} {b degree : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary) : Prop :=
  ∀ (S T U V : SelectorCoordinates b degree) (i j : Base),
    S.val ∪ T.val = U.val ∪ V.val → w (S, i) (T, j) = w (U, i) (V, j)

end Lax342547.MomentRecovery
end
