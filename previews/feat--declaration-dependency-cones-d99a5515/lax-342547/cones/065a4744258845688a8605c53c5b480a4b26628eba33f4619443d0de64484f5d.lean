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

axiom kernel_event_bound {Ω Comp I N : Type}
    [Fintype Ω] [Fintype Comp] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Comp → Matrix N I Binary) (q : ℕ) (cap : ℝ≥0∞)
    (hcap : ∀ C : Comp → Matrix I (Fin q) Binary, q ≤ (∑ e, (C e).rank) →
      p.toOuterMeasure {o | ∀ e, A o e * C e = 0} ≤ cap) :
    p.toOuterMeasure {o | q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A o e).mulVecLin)} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * Fintype.card I * q) * cap

end Lax342547.KernelWitness
end
