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
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

open Lax342547.MomentSpace

def affinePolar {U : Type} [AddCommGroup U] (f : U → Binary) (u v : U) : Binary :=
  f (u + v) + f u + f v + f 0

def polarMatrix {I : Type} [DecidableEq I] (f : (I → Binary) → Binary) : Matrix I I Binary :=
  fun i j => affinePolar f (Pi.single i 1) (Pi.single j 1)

axiom affine_polar_matrix_rank {I W : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module Binary W] (C : LinearMap.BilinForm Binary W)
    (A : (I → Binary) →ₗ[Binary] W) (w : W) (c : Binary) :
    (polarMatrix (fun z => c + C (w + A z) (w + A z))).rank =
      Module.finrank Binary (LinearMap.range ((C + C.flip).comp A A))

end Lax342547.FormalQuadratic
end
