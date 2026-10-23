-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.QuadraticForm.Prod

-- Lax342547.MomentSpace
section
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev Rows (V : B → Type) := ∀ i, V i × V i

def cross (H : ∀ i, LinearMap.BilinForm K (V i)) : LinearMap.BilinForm K (Rows V) :=
  ∑ i, (H i).comp ((LinearMap.fst K (V i) (V i)).comp (LinearMap.proj i))
    ((LinearMap.snd K (V i) (V i)).comp (LinearMap.proj i))

def quadratic (H : ∀ i, LinearMap.BilinForm K (V i)) : QuadraticForm K (Rows V) :=
  (cross H).toQuadraticMap

axiom polar_rank [∀ i, FiniteDimensional K (V i)]
    (H : ∀ i, LinearMap.BilinForm K (V i)) (hH : ∀ i, (H i).Nondegenerate) :
    Module.finrank K (LinearMap.range (quadratic H).polarBilin) =
      2 * ∑ i, Module.finrank K (V i)

open Lax342547.MomentSpace

end Lax342547.FormalQuadratic
end
