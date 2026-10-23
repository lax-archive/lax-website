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

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

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
namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

def emptySelector (b degree : ℕ) : SelectorCoordinates b degree := ⟨∅, Nat.zero_le _⟩

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩

def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

end Lax342547.ConcreteGeometry
end
