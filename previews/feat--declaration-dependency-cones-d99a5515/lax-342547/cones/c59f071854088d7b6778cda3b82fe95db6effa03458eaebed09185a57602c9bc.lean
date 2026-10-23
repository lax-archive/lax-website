-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Basic

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.KernelWitness
section
namespace Lax342547.KernelWitness

open Lax342547.MomentSpace

open scoped ENNReal

axiom exists_kernel_witness {I N : Type} [Fintype I] [Fintype N]
    (A : Matrix N I Binary) (q : ℕ) :
    ∃ C : Matrix I (Fin q) Binary, A * C = 0 ∧
      min q (Module.finrank Binary (LinearMap.ker A.mulVecLin)) ≤ C.rank

end Lax342547.KernelWitness
end
