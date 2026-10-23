-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
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

-- Lax342547.JointProjectors
section
namespace Lax342547.JointProjectors

open Lax342547.MomentSpace

axiom exists_joint_decomposition {ι V : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module Binary V] [FiniteDimensional Binary V]
    (M : ι → Module.End Binary V)
    (hid : ∀ i, M i * M i = M i) (hcomm : ∀ i j, M i * M j = M j * M i) :
    ∃ P : (ι → Binary) → Module.End Binary V,
      (∑ s, P s) = 1 ∧ (∀ s, P s * P s = P s) ∧
      (∀ s t, s ≠ t → P s * P t = 0) ∧
      (∀ i s, M i * P s = s i • P s) ∧
      (∑ s, Module.finrank Binary (LinearMap.range (P s))) = Module.finrank Binary V ∧
      Nat.card {s // P s ≠ 0} ≤ Module.finrank Binary V

end Lax342547.JointProjectors
end
