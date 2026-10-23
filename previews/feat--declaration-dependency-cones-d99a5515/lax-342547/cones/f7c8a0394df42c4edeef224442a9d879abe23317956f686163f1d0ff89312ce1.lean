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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Logic.Equiv.Set
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

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

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

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.RelativeEntropy Lax342547.FiniteSampling

open scoped BigOperators

noncomputable def channelLaw {I J : Type} [Fintype I] [Fintype J]
    (_ : (I → Binary) × (J → Binary)) : ℝ :=
    1/((2 : ℝ)^Fintype.card I*2^Fintype.card J)

noncomputable def character {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (c : (I → Binary) × (J → Binary)) : ℝ := phase c.1 (A.mulVec c.2)

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

open Lax342547.MomentSpace Lax342547.ChannelCharacters Lax342547.FiniteSampling

open scoped BigOperators

noncomputable def tensorCharacter {e I J : Type} [Fintype e] [Fintype I] [Fintype J] (h : ℕ)
    (A : e → Matrix I J Binary) (c : e × Fin h → (I → Binary) × (J → Binary)) : ℝ :=
    ∏ i, character (A i.1) (c i)

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

-- Lax342547.DuplicatedMoments
section
namespace Lax342547.DuplicatedMoments

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages

open Lax342547.ChannelCharacters Lax342547.TensorCharacters Lax342547.ComponentSpaces

open Lax342547.ComponentDuals Lax342547.CoverProjection

open scoped BigOperators

axiom duplicated_even_moment_bound {e d I J Ω : Type}
    [Fintype e] [Fintype d] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq d] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : (e × d) × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (fun i : e × d => A x i.1) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^((Fintype.card d*h)*∑ a : e, (∑ i, A (sample i) a).rank)

end Lax342547.DuplicatedMoments
end
