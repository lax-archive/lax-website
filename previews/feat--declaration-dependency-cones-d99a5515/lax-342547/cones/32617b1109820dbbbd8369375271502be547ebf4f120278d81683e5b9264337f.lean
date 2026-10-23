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
namespace Lax342547
end Lax342547

namespace Lax342547.MomentSpace
end Lax342547.MomentSpace

namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def push {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X) (x : X) : ℝ := by
  classical
  exact ∑ ω, if image ω = x then ρ ω else 0

noncomputable def conditionalWeight {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (x : X) : ℝ :=
  push (fun ω => ρ ω * w ω) image x / push ρ image x

axiom conditional_weight_reconstruction {Ω X : Type} [Fintype Ω]
    (ρ w : Ω → ℝ) (image : Ω → X) (hρ : ∀ ω, 0 ≤ ρ ω)
    (hw : ∀ ω, |w ω| ≤ 1) (x : X) :
    push ρ image x * conditionalWeight ρ w image x =
      push (fun ω => ρ ω * w ω) image x

end Lax342547.PushforwardWalsh
end
