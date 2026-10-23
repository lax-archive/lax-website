-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
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

open scoped BigOperators

noncomputable def entropy {Ω : Type} [Fintype Ω] (ρ q : Ω → ℝ) : ℝ :=
  ∑ x, (ρ x * Real.log (ρ x) - ρ x * Real.log (q x))

end Lax342547.RelativeEntropy
end

-- Lax342547.EntropyLines
section
namespace Lax342547.EntropyLines

open Lax342547.RelativeEntropy

open scoped Topology BigOperators

open Filter

noncomputable def mix {Ω : Type} (ρ ρ' : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun x => (1-t)*ρ x+t*ρ' x

noncomputable def coordinate (p q : ℝ) : ℝ := p*Real.log p-p*Real.log q

noncomputable def oldEntropy {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ x, if ρ x = 0 then 0 else coordinate (mix ρ ρ' t x) (q x)

axiom old_entropy_zero {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) :
    oldEntropy ρ ρ' q 0 = entropy ρ q

end Lax342547.EntropyLines
end
