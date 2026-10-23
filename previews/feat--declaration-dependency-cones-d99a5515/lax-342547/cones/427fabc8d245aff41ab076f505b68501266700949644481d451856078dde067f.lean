-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Pi

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

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

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm
end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

end Lax342547.TagGeometry
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def free {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (2, i)

/-- The action on all coefficient vectors induced by a common Z-coordinate change. -/
def changeZ {k n b degree : ℕ} (A : Matrix (Fin n) (Fin n) Binary) :
    Vector k n b degree →ₗ[Binary] Vector k n b degree where
  toFun v c := match c.2 with
    | some (Sum.inr (q, i)) => if q = 2 then ∑ j, A i j * v (c.1, some (free j)) else v c
    | _ => v c
  map_add' v w := by
    ext ⟨S, c⟩
    cases c with
    | none => rfl
    | some c =>
      cases c with
      | inl c => rfl
      | inr c =>
        rcases c with ⟨q, i⟩
        by_cases hq : q = 2 <;> simp [hq, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    ext ⟨S, c⟩
    cases c with
    | none => rfl
    | some c =>
      cases c with
      | inl c => rfl
      | inr c =>
        rcases c with ⟨q, i⟩
        by_cases hq : q = 2 <;> simp [hq, Finset.mul_sum, mul_left_comm]

end Lax342547.ConcreteGeometry
end
