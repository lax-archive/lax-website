-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

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

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

def form (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) : LinearMap.BilinForm Binary X :=
  rankOne a a + (∑ t, (rankOne (aTag t) (bTag t) + rankOne (bTag t) (aTag t))) + B + B.flip

axiom form_properties (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) :
    (∀ x y, form a aTag bTag B x y = form a aTag bTag B y x) ∧
      ∀ x, form a aTag bTag B x x = a x

end Lax342547.GradientForm
end
