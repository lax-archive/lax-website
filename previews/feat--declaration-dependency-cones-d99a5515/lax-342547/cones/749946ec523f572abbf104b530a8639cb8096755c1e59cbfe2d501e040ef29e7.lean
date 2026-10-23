-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
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

-- Lax342547.BinaryPrescriptions
section
namespace Lax342547.BinaryPrescriptions
end Lax342547.BinaryPrescriptions
end

-- Lax342547.SymmetricPrescriptions
section
namespace Lax342547.SymmetricPrescriptions
end Lax342547.SymmetricPrescriptions
end

-- Lax342547.RecipeRows
section
namespace Lax342547.RecipeRows

open Lax342547.MomentSpace Lax342547.BinaryPrescriptions

axiom recipe_matrix {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (a opposite p : I ⊕ J → Binary)
    (hrole₁ : (∑ i : I, a (Sum.inl i)) + (∑ i : I, opposite (Sum.inl i)) = 1)
    (hrole₂ : (∑ j : J, a (Sum.inr j)) + (∑ j : J, opposite (Sum.inr j)) = 1)
    (hcoupled : (∑ i : I, (p (Sum.inl i) + opposite (Sum.inl i))) =
      ∑ j : J, (p (Sum.inr j) + opposite (Sum.inr j))) :
    ∃ M : Matrix (I ⊕ J) (I ⊕ J) Binary, (∀ x y, M x y = M y x) ∧
      (∀ x, M x x = a x) ∧
      (∀ i : I, a (Sum.inl i) + ∑ t : I, M (Sum.inl t) (Sum.inl i) = 0) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : I, M (Sum.inl t) (Sum.inr j) = p (Sum.inr j)) ∧
      (∀ j : J, a (Sum.inr j) + ∑ t : J, M (Sum.inr t) (Sum.inr j) = 0) ∧
      (∀ i : I, a (Sum.inl i) + ∑ t : J, M (Sum.inr t) (Sum.inl i) = p (Sum.inl i))

end Lax342547.RecipeRows
end
