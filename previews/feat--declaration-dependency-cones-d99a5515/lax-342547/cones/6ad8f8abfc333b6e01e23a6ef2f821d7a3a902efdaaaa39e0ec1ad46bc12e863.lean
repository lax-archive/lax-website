-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
end Lax342547.FourierTests
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def push {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X) (x : X) : ℝ := by
  classical
  exact ∑ ω, if image ω = x then ρ ω else 0

end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.GramTests
section
namespace Lax342547.GramTests

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.PushforwardWalsh

open Lax342547.FourierTests

axiom paper_image_walsh {ΩA ΩB I : Type} [Fintype ΩA] [Fintype ΩB]
    [Fintype I] [DecidableEq I]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (imageA : ΩA → I → Binary) (imageB : ΩB → I → Binary)
    (f : ΩA → ℝ) (g : ΩB → ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1)
    (hcapA : ∀ x, push α imageA x ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hcapB : ∀ y, push β imageB y ≤ (2 : ℝ)^(-(95/100 : ℝ)*Fintype.card I))
    (hf : ∀ a, |f a| ≤ 1) (hg : ∀ b, |g b| ≤ 1) :
    |∑ a, ∑ b, α a * β b * f a * g b * phase (imageA a) (imageB b)| ≤
      (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card I)

end Lax342547.GramTests
end
