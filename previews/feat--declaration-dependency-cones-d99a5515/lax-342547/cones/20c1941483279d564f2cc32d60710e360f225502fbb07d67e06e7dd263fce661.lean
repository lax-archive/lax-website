-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Real.Lemmas

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

end Lax342547.FourierTests
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh
end Lax342547.PushforwardWalsh
end

-- Lax342547.RetainedImages
section
namespace Lax342547.RetainedImages
end Lax342547.RetainedImages
end

-- Lax342547.RelativeEntropy
section
namespace Lax342547.RelativeEntropy
end Lax342547.RelativeEntropy
end

-- Lax342547.ConditionedMixing
section
namespace Lax342547.ConditionedMixing

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.FourierTests

open scoped BigOperators

axiom conditional_test_comparison {Ω S : Type} [Fintype Ω] [Fintype S] [DecidableEq S]
    (ρ f : Ω → ℝ) (bits : Ω → S → Binary) (target : S → Binary) (ε : ℝ)
    (hε : 0 ≤ ε) (htotal : ∑ ω,ρ ω = 1) (hmean : |∑ ω,ρ ω*f ω| ≤ 1)
    (hraw : ∀ t : S → Binary,t ≠ 0 → |characterMean ρ bits target t| ≤ ε)
    (htest : ∀ t : S → Binary,t ≠ 0 → |characterMean (fun ω => ρ ω*f ω) bits target t| ≤ ε)
    (hmass : 0 < patternMass ρ bits target) :
    |patternMass (fun ω => ρ ω*f ω) bits target/patternMass ρ bits target-
      (∑ ω,ρ ω*f ω)| ≤ 2*ε/patternMass ρ bits target

end Lax342547.ConditionedMixing
end
