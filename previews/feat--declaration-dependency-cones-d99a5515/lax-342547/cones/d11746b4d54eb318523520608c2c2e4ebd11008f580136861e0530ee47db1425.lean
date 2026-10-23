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

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

end Lax342547.Walsh
end

-- Lax342547.FourierTests
section
namespace Lax342547.FourierTests

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def patternMass {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) : ℝ := by
  classical
  exact ∑ ω, if bits ω = target then ρ ω else 0

noncomputable def characterMean {Ω I : Type} [Fintype Ω] [Fintype I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target t : I → Binary) : ℝ :=
  ∑ ω, ρ ω * phase t (bits ω) * phase t target

axiom pattern_lower {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]
    (ρ : Ω → ℝ) (bits : Ω → I → Binary) (target : I → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (hρ : ∑ ω, ρ ω = 1)
    (hchar : ∀ t : I → Binary, t ≠ 0 → -ε ≤ characterMean ρ bits target t) :
    1 / (2 : ℝ) ^ Fintype.card I - ε ≤ patternMass ρ bits target

end Lax342547.FourierTests
end
