-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.SelectorInterpolation
section
namespace Lax342547.SelectorInterpolation

open Lax342547.MomentSpace

axiom selectorEval_linearIndependent {ι : Type} [Fintype ι] {b degree : ℕ}
    (s : ι → Fin b → Binary) (hs : Function.Injective s)
    (hdegree : Fintype.card ι ≤ degree + 1) :
    LinearIndependent Binary (fun i => selectorEval (degree := degree) (s i))

end Lax342547.SelectorInterpolation
end
