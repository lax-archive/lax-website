-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
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
end Lax342547.Walsh
end

-- Lax342547.PushforwardWalsh
section
namespace Lax342547.PushforwardWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def push {Ω X : Type} [Fintype Ω] (ρ : Ω → ℝ) (image : Ω → X) (x : X) : ℝ := by
  classical
  exact ∑ ω, if image ω = x then ρ ω else 0

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

open Lax342547.RetainedImages Lax342547.PushforwardWalsh

open scoped ENNReal

noncomputable def weights {Ω : Type} (p : PMF Ω) : Ω → ℝ := fun ω => (p ω).toReal

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
end Lax342547.FiniteSampling
end

-- Lax342547.AcceptingFamilies
section
namespace Lax342547.AcceptingFamilies
end Lax342547.AcceptingFamilies
end

-- Lax342547.AmplifiedTests
section
namespace Lax342547.AmplifiedTests
end Lax342547.AmplifiedTests
end

-- Lax342547.GreedySpaces
section
namespace Lax342547.GreedySpaces
end Lax342547.GreedySpaces
end

-- Lax342547.SequentialTests
section
namespace Lax342547.SequentialTests
end Lax342547.SequentialTests

namespace Lax342547.SequentialTests.accepts
end Lax342547.SequentialTests.accepts
end

-- Lax342547.IndependentSampling
section
namespace Lax342547.IndependentSampling
end Lax342547.IndependentSampling
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

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns
end Lax342547.GramColumns
end

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization
end Lax342547.GramNormalization
end

-- Lax342547.ChannelDensity
section
namespace Lax342547.ChannelDensity
end Lax342547.ChannelDensity
end

-- Lax342547.FiniteMoments
section
namespace Lax342547.FiniteMoments
end Lax342547.FiniteMoments
end

-- Lax342547.MomentTails
section
namespace Lax342547.MomentTails
end Lax342547.MomentTails
end

-- Lax342547.BilinearWalsh
section
namespace Lax342547.BilinearWalsh
end Lax342547.BilinearWalsh
end

-- Lax342547.BilinearMean
section
namespace Lax342547.BilinearMean
end Lax342547.BilinearMean
end

-- Lax342547.ChannelCharacters
section
namespace Lax342547.ChannelCharacters
end Lax342547.ChannelCharacters
end

-- Lax342547.ChannelMoments
section
namespace Lax342547.ChannelMoments
end Lax342547.ChannelMoments
end

-- Lax342547.TensorCharacters
section
namespace Lax342547.TensorCharacters
end Lax342547.TensorCharacters
end

-- Lax342547.ComponentMoments
section
namespace Lax342547.ComponentMoments
end Lax342547.ComponentMoments
end

-- Lax342547.DyadicDeficits
section
namespace Lax342547
end Lax342547

namespace Lax342547.DyadicDeficits
end Lax342547.DyadicDeficits
end

-- Lax342547.DyadicTails
section
namespace Lax342547.DyadicTails
end Lax342547.DyadicTails
end

-- Lax342547.DyadicScale
section
namespace Lax342547.DyadicScale
end Lax342547.DyadicScale
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.SpanDeficits
section
namespace Lax342547.SpanDeficits
end Lax342547.SpanDeficits
end

-- Lax342547.GreedySpans
section
namespace Lax342547.GreedySpans
end Lax342547.GreedySpans

namespace Lax342547.GreedySpans.Greedy
end Lax342547.GreedySpans.Greedy
end

-- Lax342547.ListTails
section
namespace Lax342547.ListTails
end Lax342547.ListTails
end

-- Lax342547.GreedyTails
section
namespace Lax342547.GreedyTails
end Lax342547.GreedyTails
end

-- Lax342547.ProjectedSpans
section
namespace Lax342547.ProjectedSpans
end Lax342547.ProjectedSpans
end

-- Lax342547.ActualDeficits
section
namespace Lax342547.ActualDeficits
end Lax342547.ActualDeficits
end

-- Lax342547.MappedSpans
section
namespace Lax342547.MappedSpans
end Lax342547.MappedSpans
end

-- Lax342547.SpanDeficitMono
section
namespace Lax342547.SpanDeficitMono
end Lax342547.SpanDeficitMono
end

-- Lax342547.DirectRanks
section
namespace Lax342547.DirectRanks
end Lax342547.DirectRanks
end

-- Lax342547.QuotientRank
section
namespace Lax342547.QuotientRank
end Lax342547.QuotientRank
end

-- Lax342547.RankLoss
section
namespace Lax342547.RankLoss
end Lax342547.RankLoss
end

-- Lax342547.BlockDeficits
section
namespace Lax342547.BlockDeficits
end Lax342547.BlockDeficits
end

-- Lax342547.SumRank
section
namespace Lax342547.SumRank
end Lax342547.SumRank
end

-- Lax342547.SumEnvelope
section
namespace Lax342547.SumEnvelope
end Lax342547.SumEnvelope
end

-- Lax342547.ListDeficits
section
namespace Lax342547.ListDeficits
end Lax342547.ListDeficits
end

-- Lax342547.ModeBudgets
section
namespace Lax342547.ModeBudgets
end Lax342547.ModeBudgets
end

-- Lax342547.CoverClasses
section
namespace Lax342547.CoverClasses
end Lax342547.CoverClasses
end

-- Lax342547.ComponentSpaces
section
namespace Lax342547.ComponentSpaces
end Lax342547.ComponentSpaces
end

-- Lax342547.ComponentDuals
section
namespace Lax342547.ComponentDuals
end Lax342547.ComponentDuals
end

-- Lax342547.CoordinateRestrictions
section
namespace Lax342547.CoordinateRestrictions
end Lax342547.CoordinateRestrictions
end

-- Lax342547.AdaptiveSampling
section
namespace Lax342547.AdaptiveSampling
end Lax342547.AdaptiveSampling
end

-- Lax342547.AdaptiveSets
section
namespace Lax342547.AdaptiveSets
end Lax342547.AdaptiveSets
end

-- Lax342547.AdaptiveUnion
section
namespace Lax342547.AdaptiveUnion
end Lax342547.AdaptiveUnion
end

-- Lax342547.CombinedSpans
section
namespace Lax342547.CombinedSpans
end Lax342547.CombinedSpans
end

-- Lax342547.SmallExposure
section
namespace Lax342547.SmallExposure
end Lax342547.SmallExposure
end

-- Lax342547.CoverCounts
section
namespace Lax342547.CoverCounts
end Lax342547.CoverCounts
end

-- Lax342547.CoverProjection
section
namespace Lax342547.CoverProjection
end Lax342547.CoverProjection
end

-- Lax342547.PartitionLists
section
namespace Lax342547.PartitionLists
end Lax342547.PartitionLists
end

-- Lax342547.ExposedSums
section
namespace Lax342547.ExposedSums
end Lax342547.ExposedSums
end

-- Lax342547.FilterOccurrences
section
namespace Lax342547.FilterOccurrences
end Lax342547.FilterOccurrences
end

-- Lax342547.ProjectedCounts
section
namespace Lax342547.ProjectedCounts
end Lax342547.ProjectedCounts
end

-- Lax342547.NoCoverCertificate
section
namespace Lax342547.NoCoverCertificate
end Lax342547.NoCoverCertificate
end

-- Lax342547.NoCoverRank
section
namespace Lax342547.NoCoverRank
end Lax342547.NoCoverRank
end

-- Lax342547.IndexedRankGrowth
section
namespace Lax342547.IndexedRankGrowth
end Lax342547.IndexedRankGrowth
end

-- Lax342547.NoCoverMoments
section
namespace Lax342547.NoCoverMoments
end Lax342547.NoCoverMoments
end

-- Lax342547.ChannelColumns
section
namespace Lax342547.ChannelColumns
end Lax342547.ChannelColumns
end

-- Lax342547.InjectiveFrames
section
namespace Lax342547.InjectiveFrames
end Lax342547.InjectiveFrames
end

-- Lax342547.ProtectedChannels
section
namespace Lax342547.ProtectedChannels
end Lax342547.ProtectedChannels
end

-- Lax342547.SmallSubspaceCount
section
namespace Lax342547.SmallSubspaceCount
end Lax342547.SmallSubspaceCount
end

-- Lax342547.AdaptiveProtection
section
namespace Lax342547.AdaptiveProtection
end Lax342547.AdaptiveProtection
end

-- Lax342547.IndependentWitnesses
section
namespace Lax342547.IndependentWitnesses
end Lax342547.IndependentWitnesses
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.TotalRankCount
section
namespace Lax342547.TotalRankCount
end Lax342547.TotalRankCount
end

-- Lax342547.UniformPhaseTails
section
namespace Lax342547.UniformPhaseTails
end Lax342547.UniformPhaseTails
end

-- Lax342547.PhaseAverages
section
namespace Lax342547.PhaseAverages
end Lax342547.PhaseAverages
end

-- Lax342547.UniversalWitnesses
section
namespace Lax342547.UniversalWitnesses
end Lax342547.UniversalWitnesses
end

-- Lax342547.FiniteInjection
section
namespace Lax342547.FiniteInjection

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling

open Lax342547.RealCellLaws Lax342547.PushforwardWalsh

open scoped BigOperators

def pinFailure {N H : Type} [Fintype N] (V : Submodule Binary (N → Binary))
    (Y : Matrix N H Binary) (S : Submodule Binary (H → Binary)) : Prop :=
  ∃ v : V,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S

end Lax342547.FiniteInjection
end

-- Lax342547.InjectiveDensity
section
namespace Lax342547.InjectiveDensity
end Lax342547.InjectiveDensity
end

-- Lax342547.PrimalAvoidance
section
namespace Lax342547.PrimalAvoidance
end Lax342547.PrimalAvoidance
end

-- Lax342547.RawPrimalAvoidance
section
namespace Lax342547.RawPrimalAvoidance
end Lax342547.RawPrimalAvoidance
end

-- Lax342547.UnitSpanAvoidance
section
namespace Lax342547.UnitSpanAvoidance
end Lax342547.UnitSpanAvoidance
end

-- Lax342547.AcceptingInjection
section
namespace Lax342547.AcceptingInjection
end Lax342547.AcceptingInjection
end

-- Lax342547.MomentBudgets
section
namespace Lax342547.MomentBudgets
end Lax342547.MomentBudgets
end

-- Lax342547.InjectionBudgets
section
namespace Lax342547.InjectionBudgets
end Lax342547.InjectionBudgets
end

-- Lax342547.RawAcceptingInjection
section
namespace Lax342547.RawAcceptingInjection

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages

open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.FiniteInjection

open Lax342547.RawFrames Lax342547.FrameSymmetry

open scoped BigOperators

axiom exponential_accepting_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (imageA : A → Frame P H N E) (imageB : B → Frame P H N E)
    (V : A → Submodule Binary (N → Binary)) (S : B → Submodule Binary (H → Binary))
    (K m t Cs : ℕ) (M MB η : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hMB : 0 ≤ MB)
    (hη : 0 ≤ η) (hηt : 1/(2 : ℝ)^t ≤ η/2)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hb : Fintype.card P ≤ Fintype.card N/8)
    (hm : m+Fintype.card H+1 ≤ Fintype.card N/10)
    (hMcap : M ≤ (2 : ℝ)^m) (hMBcap : 2*MB ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hearly : 2*K+t+20*(K+1)*(Cs+3) ≤ Fintype.card H)
    (hlength : 20*(K+1) ≤ Fintype.card N)
    (hconstant : m+Fintype.card H*K ≤ Fintype.card N)
    (hsmall : 1/(2 : ℝ)^(Fintype.card N/2) ≤ η/2)
    (hV : ∀ a,V a ≤ LinearMap.range (imageA a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α imageA f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ f,push β imageB f ≤ MB*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (imageB b).Y (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + 1/(2 : ℝ)^(Fintype.card N/100) + 1/(2 : ℝ)^Fintype.card N

end Lax342547.RawAcceptingInjection
end
