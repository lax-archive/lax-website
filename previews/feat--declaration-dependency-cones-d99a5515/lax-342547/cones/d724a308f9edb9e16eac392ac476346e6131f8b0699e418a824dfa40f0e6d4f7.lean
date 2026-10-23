-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh

open Lax342547.MomentSpace

def bitMatrix {I J : Type} (C : Matrix I J Binary) (N : ℕ) :
    Matrix (Fin N × I) (Fin N × J) Binary :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

axiom bit_evaluation {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) (N : ℕ) (x : Fin N × I → Binary) (y : Fin N × J → Binary) :
    dotProduct x ((bitMatrix C N).mulVec y) = ∑ i, ∑ j, C i j * ∑ a, x (a, i) * y (a, j)

end Lax342547.SlotWalsh
end
