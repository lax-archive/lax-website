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

axiom two_lists {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a c₁ c₂ : I ⊕ J → Binary)
    (h₁ : ∑ i : I, c₁ (Sum.inl i) = ∑ i : I, a (Sum.inl i))
    (h₂ : ∑ j : J, c₂ (Sum.inr j) = ∑ j : J, a (Sum.inr j))
    (hcross : ∑ i : I, c₂ (Sum.inl i) = ∑ j : J, c₁ (Sum.inr j)) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) Binary, (∀ x y, M x y = M y x) ∧
      (∀ x, M x x = a x) ∧ (∀ x, ∑ i : I, M x (Sum.inl i) = c₁ x) ∧
      ∀ x, ∑ j : J, M x (Sum.inr j) = c₂ x

end Lax342547.SymmetricPrescriptions
end
