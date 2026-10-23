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

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

noncomputable def conditionalLaw {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : Ω → ℝ := by
  classical
  exact fun ω => (if C ω then ρ ω else 0) / cellMass ρ C

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

open Lax342547.MomentSpace

def bitMatrix {I J : Type} (C : Matrix I J Binary) (N : ℕ) :
    Matrix (Fin N × I) (Fin N × J) Binary :=
  fun x y => if x.1 = y.1 then C x.2 y.2 else 0

end Lax342547.SlotWalsh
end

-- Lax342547.CrossBatchMixing
section
namespace Lax342547.CrossBatchMixing

open Lax342547.MomentSpace Lax342547.SlotWalsh Lax342547.FourierTests Lax342547.RelativeEntropy

def crossBits {I J S : Type} [Fintype I] [Fintype J] (C : S → Matrix I J Binary) (N : ℕ)
    (xy : ((Fin N × I → Binary) × (Fin N × J → Binary))) : S → Binary :=
  fun s => dotProduct xy.1 ((bitMatrix (C s) N).mulVec xy.2)

end Lax342547.CrossBatchMixing
end

-- Lax342547.CrossGramBasis
section
namespace Lax342547.CrossGramBasis

open Lax342547.MomentSpace Lax342547.CrossBatchMixing

open scoped BigOperators

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

abbrev Slots (I J K L : Type) := (I × L) ⊕ (J × K)

def tests {I J K L : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] :
    Slots I J K L → Matrix (I ⊕ J) (K ⊕ L) Binary
  | Sum.inl (i,l) => fun a b => if a = Sum.inl i ∧ b = Sum.inr l then 1 else 0
  | Sum.inr (j,k) => fun a b => if a = Sum.inr j ∧ b = Sum.inl k then 1 else 0

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

def Good (z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) :=
  Function.Injective (ambientEquiv z).1.mulVec ∧ Function.Injective (ambientEquiv z).2.mulVec

end

end Lax342547.JointGramInjection
end

-- Lax342547.RawBatchComparison
section
namespace Lax342547.RawBatchComparison

noncomputable section

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

open Lax342547.GramOrbitDensity Lax342547.RetainedImages

open scoped BigOperators

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

def target (A : Matrix I L Binary) (B : Matrix K J Binary) :
    Lax342547.CrossGramBasis.Slots I J K L → Binary
  | Sum.inl (i,l) => A i l
  | Sum.inr (j,k) => B k j

axiom union_conditional_integral (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (test : ((Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary)) → ℝ) :
    (∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),
      weights (PMF.uniformOfFintype _) z*test (Lax342547.JointGramInjection.ambientEquiv.symm z.val)) =
    ∑ x,conditionalLaw (fun x => batchLaw G x.1*batchLaw H x.2)
      (fun x => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n x = target A B ∧
        Lax342547.JointGramInjection.Good x) x*test x

end

end Lax342547.RawBatchComparison
end
