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
namespace Lax342547.CrossGramBasis.tests
end Lax342547.CrossGramBasis.tests

namespace Lax342547.CrossGramBasis

open Lax342547.MomentSpace Lax342547.CrossBatchMixing

open scoped BigOperators

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

abbrev Slots (I J K L : Type) := (I × L) ⊕ (J × K)

end Lax342547.CrossGramBasis
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

noncomputable section

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

open Lax342547.GramOrbitDensity Lax342547.RawFrames

open scoped BigOperators

def errorBound (n : ℕ) (I J K L : Type) [Fintype I] [Fintype J] [Fintype K] [Fintype L] : ℝ :=
  (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
    ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
      ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
      (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
        (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)))

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable {B H : Type} [Fintype B] [Fintype H]

end

end Lax342547.RawFrameComparison
end
