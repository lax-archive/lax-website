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
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
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

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

abbrev Orbit {I J : Type} (N : Type) [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) :=
  {z : Matrix N I Binary × Matrix N J Binary //
    Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

noncomputable instance {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (G : Matrix I J Binary) : Fintype (Orbit N G) := by classical exact Subtype.fintype _

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

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

open Lax342547.RetainedImages Lax342547.PushforwardWalsh

open scoped ENNReal

noncomputable def weights {Ω : Type} (p : PMF Ω) : Ω → ℝ := fun ω => (p ω).toReal

end Lax342547.RealCellLaws
end

-- Lax342547.GramOrbitDensity
section
namespace Lax342547.GramOrbitDensity

open Lax342547.RelativeEntropy

open scoped BigOperators

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

def batchEquiv {I J N : Type} :
    (Matrix N I Binary × Matrix N J Binary) ≃ (N × (I ⊕ J) → Binary) where
  toFun z p := match p.2 with
    | Sum.inl i => z.1 p.1 i
    | Sum.inr j => z.2 p.1 j
  invFun x := (fun n i => x (n,Sum.inl i),fun n j => x (n,Sum.inr j))
  left_inv z := rfl
  right_inv x := by funext p; rcases p with ⟨n,i|j⟩ <;> rfl

noncomputable def batchLaw {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq N] (G : Matrix I J Binary) [Nonempty (Orbit N G)] :
    (N × (I ⊕ J) → Binary) → ℝ :=
  weights ((PMF.uniformOfFintype (Orbit N G)).map (fun z => batchEquiv z.val))

end Lax342547.GramOrbitDensity
end

-- Lax342547.JointGramInjection
section
namespace Lax342547.JointGramInjection

noncomputable section

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

open Lax342547.GramOrbitDensity Lax342547.RetainedImages

open scoped BigOperators ENNReal

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

def ambientEquiv :
    ((N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) ≃
      (Matrix N (I ⊕ K) Binary × Matrix N (J ⊕ L) Binary) where
  toFun z := (Matrix.fromCols (batchEquiv.symm z.1).1 (batchEquiv.symm z.2).1,
    Matrix.fromCols (batchEquiv.symm z.1).2 (batchEquiv.symm z.2).2)
  invFun z := (batchEquiv (z.1.submatrix id Sum.inl,z.2.submatrix id Sum.inl),
    batchEquiv (z.1.submatrix id Sum.inr,z.2.submatrix id Sum.inr))
  left_inv z := by apply Prod.ext <;> funext (n,s) <;> cases s <;> rfl
  right_inv z := by apply Prod.ext <;> ext n (i | k) <;> rfl

end

end Lax342547.JointGramInjection
end

-- Lax342547.RawBatchComparison
section
namespace Lax342547.RawBatchComparison.target
end Lax342547.RawBatchComparison.target

namespace Lax342547.RawBatchComparison

noncomputable section

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

open Lax342547.GramOrbitDensity Lax342547.RetainedImages

open scoped BigOperators

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

axiom union_test_comparison (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),weights (PMF.uniformOfFintype _) z*
        (f (Lax342547.JointGramInjection.ambientEquiv.symm z.val).1*
          g (Lax342547.JointGramInjection.ambientEquiv.symm z.val).2))-
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
          (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
            ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
            (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)))

end

end Lax342547.RawBatchComparison
end
