-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Distributions.Uniform
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

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry
end Lax342547.FrameSymmetry

namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change
end

-- Lax342547.FrameTuples
section
namespace Lax342547.FrameTuples
end Lax342547.FrameTuples
end

-- Lax342547.JoinedGramOrbits
section
namespace Lax342547.JoinedGramOrbits
end Lax342547.JoinedGramOrbits
end

-- Lax342547.Walsh
section
namespace Lax342547.Walsh
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

def Probability {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∑ x, ρ x = 1

end Lax342547.RelativeEntropy
end

-- Lax342547.ConditionedMixing
section
namespace Lax342547.ConditionedMixing
end Lax342547.ConditionedMixing
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.SlotWalsh
section
namespace Lax342547.SlotWalsh
end Lax342547.SlotWalsh
end

-- Lax342547.CrossBatchMixing
section
namespace Lax342547.CrossBatchMixing
end Lax342547.CrossBatchMixing
end

-- Lax342547.CrossGramBasis
section
namespace Lax342547.CrossGramBasis
end Lax342547.CrossGramBasis

namespace Lax342547.CrossGramBasis.tests
end Lax342547.CrossGramBasis.tests
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

-- Lax342547.GramOrbitDensity
section
namespace Lax342547.GramOrbitDensity
end Lax342547.GramOrbitDensity

namespace Lax342547.GramOrbitDensity.batchEquiv
end Lax342547.GramOrbitDensity.batchEquiv
end

-- Lax342547.JointGramInjection
section
namespace Lax342547.JointGramInjection
end Lax342547.JointGramInjection

namespace Lax342547.JointGramInjection.ambientEquiv
end Lax342547.JointGramInjection.ambientEquiv
end

-- Lax342547.RawBatchComparison
section
namespace Lax342547.RawBatchComparison
end Lax342547.RawBatchComparison

namespace Lax342547.RawBatchComparison.target
end Lax342547.RawBatchComparison.target
end

-- Lax342547.RawFrameComparison
section
namespace Lax342547.RawFrameComparison
end Lax342547.RawFrameComparison
end

-- Lax342547.GroupTensorComparison
section
namespace Lax342547.GroupTensorComparison

noncomputable section

open Lax342547.RelativeEntropy

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type} [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)]

def mean (ρ : ∀ i,X i × Y i → ℝ) (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ) : ℝ :=
  ∑ z : ∀ i,X i × Y i,(∏ i,ρ i (z i))*f (fun i => (z i).1)*g (fun i => (z i).2)

axiom reference_product_comparison (ρ : ∀ i,X i × Y i → ℝ)
    (α : ∀ i,X i → ℝ) (β : ∀ i,Y i → ℝ)
    (hρ : ∀ i,Probability (ρ i)) (hα : ∀ i,Probability (α i)) (hβ : ∀ i,Probability (β i))
    (ε : ι → ℝ)
    (hc : ∀ i,∀ f : X i → ℝ,∀ g : Y i → ℝ,(∀ x,|f x| ≤ 1) → (∀ y,|g y| ≤ 1) →
      |(∑ z : X i × Y i,ρ i z*f z.1*g z.2)-
        (∑ x,α i x*f x)*(∑ y,β i y*g y)| ≤ ε i)
    (f : (∀ i,X i) → ℝ) (g : (∀ i,Y i) → ℝ)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1) :
    |mean ρ f g-(∑ x,(∏ i,α i (x i))*f x)*(∑ y,(∏ i,β i (y i))*g y)| ≤ ∑ i,ε i

end

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {X Y Ω : ι → Type} [∀ i,Fintype (Ω i)] [∀ i,Nonempty (Ω i)]

open Lax342547.RealCellLaws

end

end Lax342547.GroupTensorComparison
end
