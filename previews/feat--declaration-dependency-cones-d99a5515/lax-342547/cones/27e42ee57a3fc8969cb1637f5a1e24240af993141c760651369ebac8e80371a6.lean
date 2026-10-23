-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

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
end Lax342547.EntropyProjection
end

-- Lax342547.Conditioning
section
namespace Lax342547
end Lax342547

namespace Lax342547.Conditioning
end Lax342547.Conditioning
end

-- Lax342547.RealCellLaws
section
namespace Lax342547.RealCellLaws
end Lax342547.RealCellLaws
end

-- Lax342547.PairRecovery
section
namespace Lax342547.PairRecovery
end Lax342547.PairRecovery
end

-- Lax342547.UnitLaws
section
namespace Lax342547.UnitLaws
end Lax342547.UnitLaws
end

-- Lax342547.ContainerLaws
section
namespace Lax342547.ContainerLaws

open Lax342547.RelativeEntropy Lax342547.RetainedImages

open scoped BigOperators

noncomputable def residual {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U) : Set (U → ℝ) :=
  {ρ | ρ ∈ P ∧ ∀ x, x ∉ R → ρ x = 0}

noncomputable def neighborMass {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop) (v : U) : ℝ :=
  cellMass ρ (H v)

axiom recording_entropy_increment {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q ρ σ : U → ℝ) (R : Finset U) (H : U → U → Prop) (v : U) (ε : ℝ)
    (hprob : ∀ τ ∈ P, Probability τ) (hconv : Convex ℝ P)
    (hρ : ρ ∈ residual P R) (hmin : ∀ τ ∈ residual P R, entropy ρ q ≤ entropy τ q)
    (hσ : σ ∈ residual P R ∧ ∀ x, H v x → σ x = 0)
    (_hε : ε < 1) (hheavy : ε ≤ neighborMass ρ H v) :
    -Real.log (1-ε) ≤ entropy σ q-entropy ρ q

end Lax342547.ContainerLaws
end
