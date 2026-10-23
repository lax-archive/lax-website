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

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

structure Frame (E : Matrix B B Binary) where
  P : Matrix N B Binary
  Q : Matrix N B Binary
  X : Matrix N H Binary
  Y : Matrix N H Binary
  plus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)
  minus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)
  gram : P.transpose * Q = E
  plus_annihilator : X.transpose * Q = 0
  minus_annihilator : P.transpose * Y = 0

variable {B H N}

abbrev FrameData := Matrix N B Binary × Matrix N B Binary × Matrix N H Binary × Matrix N H Binary

def frameData {E : Matrix B B Binary} (F : Frame B H N E) : FrameData (B := B) (H := H) (N := N) :=
  (F.P, F.Q, F.X, F.Y)

theorem frameData_injective {E : Matrix B B Binary} :
    Function.Injective (frameData (E := E) (H := H) (N := N)) := by
  intro F G h
  cases F
  cases G
  simp only [frameData, Prod.mk.injEq] at h
  obtain ⟨hP, hQ, hX, hY⟩ := h
  cases hP
  cases hQ
  cases hX
  cases hY
  rfl

noncomputable instance {E : Matrix B B Binary} : Fintype (Frame B H N E) :=
  by classical exact Fintype.ofInjective frameData frameData_injective

variable {Comp : Type}

end Lax342547.RawFrames
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

end Lax342547.GramOrbitDensity
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

-- Lax342547.GroupTensorComparison
section
namespace Lax342547.GroupTensorComparison
end Lax342547.GroupTensorComparison
end

-- Lax342547.RawGroupedComparison
section
namespace Lax342547.RawGroupedComparison

noncomputable section

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.GramOrbitDensity

open Lax342547.FrameTuples Lax342547.RealCellLaws Lax342547.RawFrameComparison

open scoped BigOperators

variable {S B H : Type} [Fintype S] [DecidableEq S] [Fintype B] [Fintype H]
  {I J K L : S → Type} [∀ s,Fintype (I s)] [∀ s,Fintype (J s)]
  [∀ s,Fintype (K s)] [∀ s,Fintype (L s)]

axiom primal_groups [∀ s,DecidableEq (I s)] [∀ s,DecidableEq (J s)]
    [∀ s,DecidableEq (K s)] [∀ s,DecidableEq (L s)] (n : ℕ) (E : S → Matrix B B Binary)
    [∀ s,Nonempty (Frame B H (Fin n) (E s))]
    (C₁ : ∀ s,Matrix B (I s) Binary) (D₁ : ∀ s,Matrix B (J s) Binary)
    (C₂ : ∀ s,Matrix B (K s) Binary) (D₂ : ∀ s,Matrix B (L s) Binary)
    (hC : ∀ s,Function.Injective (Matrix.fromCols (C₁ s) (C₂ s)).mulVec)
    (hD : ∀ s,Function.Injective (Matrix.fromCols (D₁ s) (D₂ s)).mulVec)
    (f : (∀ s,Fin n × (I s ⊕ J s) → Binary) → ℝ)
    (g : (∀ s,Fin n × (K s ⊕ L s) → Binary) → ℝ)
    (hN₁ : ∀ s,Fintype.card (I s)+Fintype.card (J s)+1 ≤ n)
    (hN₂ : ∀ s,Fintype.card (K s)+Fintype.card (L s)+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ∀ s,((2 : ℝ)^(Fintype.card (I s)*Fintype.card (J s)+2))*
        ((2 : ℝ)^(Fintype.card (K s)*Fintype.card (L s)+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (I s) (J s) (K s) (L s))+1)) :
    |(∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        (f (fun s => batchEquiv ((o s).P*C₁ s,(o s).Q*D₁ s))*
          g (fun s => batchEquiv ((o s).P*C₂ s,(o s).Q*D₂ s))))-
      (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        f (fun s => batchEquiv ((o s).P*C₁ s,(o s).Q*D₁ s)))*
      (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        g (fun s => batchEquiv ((o s).P*C₂ s,(o s).Q*D₂ s)))| ≤
      ∑ s,errorBound n (I s) (J s) (K s) (L s)

end

end Lax342547.RawGroupedComparison
end
