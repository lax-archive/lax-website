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

def Probability {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∑ x, ρ x = 1

end Lax342547.RelativeEntropy
end

-- Lax342547.EntropyLines
section
namespace Lax342547.EntropyLines
end Lax342547.EntropyLines
end

-- Lax342547.EntropyProjection
section
namespace Lax342547.EntropyProjection

open Lax342547.RelativeEntropy Lax342547.EntropyLines

open scoped Topology BigOperators

open Filter

axiom entropy_projection {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q : Ω → ℝ) (hcompact : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (hprob : ∀ p ∈ P, Probability p) :
    ∃ ρ ∈ P, (∀ ρ' ∈ P, entropy ρ q ≤ entropy ρ' q) ∧
      (∀ ρ' ∈ P, ∀ x, 0 < ρ' x → 0 < ρ x) ∧
      (∀ ρ' ∈ P, entropy ρ' ρ ≤ entropy ρ' q-entropy ρ q)

end Lax342547.EntropyProjection
end
