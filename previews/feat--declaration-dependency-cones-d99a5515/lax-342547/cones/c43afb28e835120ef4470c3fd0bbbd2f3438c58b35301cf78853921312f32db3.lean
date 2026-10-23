-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.DFinsupp
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
end Lax342547.ContainerLaws
end

-- Lax342547.FiniteSampling
section
namespace Lax342547.FiniteSampling

open Lax342547.RelativeEntropy Lax342547.RetainedImages

open scoped BigOperators

noncomputable def productLaw {ι Ω : Type} [Fintype ι] (μ : ι → Ω → ℝ) (sample : ι → Ω) : ℝ :=
  ∏ i, μ i (sample i)

end Lax342547.FiniteSampling
end

-- Lax342547.GreedySpaces
section
namespace Lax342547.GreedySpaces
end Lax342547.GreedySpaces
end

-- Lax342547.SequentialTests
section
namespace Lax342547.SequentialTests

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling

open scoped BigOperators

def accepts {Ω : Type} (P : ∀ j,(Fin j → Ω) → Ω → Prop) : ∀ n,(Fin n → Ω) → Prop
  | 0,_ => True
  | n+1,s => accepts P n (Fin.init s) ∧ P n (Fin.init s) (s (Fin.last n))

end Lax342547.SequentialTests
end

-- Lax342547.IndependentSampling
section
namespace Lax342547.IndependentSampling

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling

open scoped BigOperators

axiom greedy_failure_lower_probability {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Fintype Ω] (U : Ω → Submodule K V) (μ : Ω → ℝ) (F : Ω → Prop)
    (η δ : ℝ) (n : ℕ) (hμ : Probability μ) (hgap : δ ≤ η)
    (hF : η ≤ cellMass μ F)
    (havoid : ∀ j,j < n → ∀ t : Fin j → Ω,
      cellMass μ (fun x => ¬ Disjoint (U x) (⨆ i : Fin j,U (t i))) ≤ δ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (fun s => Lax342547.SequentialTests.accepts
        (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n s)

end Lax342547.IndependentSampling
end
