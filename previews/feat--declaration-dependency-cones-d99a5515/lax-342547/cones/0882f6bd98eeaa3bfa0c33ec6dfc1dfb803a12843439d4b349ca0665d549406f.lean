-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Block
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

-- Lax342547.SymmetricPrescriptions
section
namespace Lax342547.SymmetricPrescriptions

open Lax342547.MomentSpace

axiom diagonal_rows {I : Type} [Fintype I] [Nonempty I]
    (a c : I → Binary) (h : ∑ i, c i = ∑ i, a i) :
    ∃ M : Matrix I I Binary, (∀ i j, M i j = M j i) ∧
      (∀ i, M i i = a i) ∧ ∀ i, ∑ j, M i j = c i

end Lax342547.SymmetricPrescriptions
end
