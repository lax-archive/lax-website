-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.BinaryPrescriptions
section
namespace Lax342547.BinaryPrescriptions

open Lax342547.MomentSpace

def productSum {I Term : Type} [Fintype Term] (L R : I → I → Term → Binary) (x y : I) : Binary :=
  ∑ t, L x y t * R x y t

axiom realize {I Term : Type} [Fintype I] [Fintype Term]
    (allowed : I → I → Term → Prop) (hallowed : ∀ x y, ∃ t, allowed x y t)
    (T₀ M : Matrix I I Binary) (hT : ∀ x y, T₀ x y = T₀ y x)
    (hM : ∀ x y, M x y = M y x) (hdiag : ∀ x, M x x = T₀ x x) :
    ∃ L R : I → I → Term → Binary,
      (∀ x y t, ¬ allowed x y t → L x y t = 0 ∧ R x y t = 0) ∧
      ∀ x y, T₀ x y + productSum L R x y + productSum L R y x = M x y

end Lax342547.BinaryPrescriptions
end
