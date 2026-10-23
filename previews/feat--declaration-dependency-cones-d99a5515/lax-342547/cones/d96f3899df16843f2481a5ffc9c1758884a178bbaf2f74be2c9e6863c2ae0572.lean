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

axiom exists_family_witness {Comp I N : Type} [Fintype Comp] [Fintype I] [Fintype N]
    (A : Comp → Matrix N I Binary) (q : ℕ)
    (hq : q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A e).mulVecLin)) :
    ∃ C : Comp → Matrix I (Fin q) Binary, (∀ e, A e * C e = 0) ∧ q ≤ ∑ e, (C e).rank

end Lax342547.KernelWitness
end
