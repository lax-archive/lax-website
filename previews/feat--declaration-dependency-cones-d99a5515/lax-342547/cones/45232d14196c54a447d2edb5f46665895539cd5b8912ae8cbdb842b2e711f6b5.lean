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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.BilinearForm.Properties
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

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

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

open Lax342547.CoverClasses

open scoped BigOperators

noncomputable def coordinateSpace {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (S : ∀ i, Submodule K (V i)) :
    Submodule K (∀ i, V i) where
  carrier := {v | ∀ i, v i ∈ S i}
  zero_mem' := fun i => (S i).zero_mem
  add_mem' := fun h g i => (S i).add_mem (h i) (g i)
  smul_mem' := fun c _ h i => (S i).smul_mem c (h i)

def Componentwise {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : Submodule K (∀ i, V i)) : Prop := ∃ S, T = coordinateSpace S

end Lax342547.ComponentSpaces
end

-- Lax342547.ComponentDuals
section
namespace Lax342547.ComponentDuals

open Lax342547.ComponentSpaces Lax342547.CoverClasses

open scoped BigOperators

def DualComponentwise {K e : Type} [Field K] [Fintype e] [DecidableEq e] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (T : Submodule K (Module.Dual K (∀ i, V i))) : Prop :=
    Componentwise (T.map (LinearMap.lsum K V K).symm.toLinearMap)

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

open Lax342547.GreedySpans

open scoped BigOperators

noncomputable def projection {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    T.dualCoannihilator →ₗ[K] (W ⧸ S) := S.mkQ.comp (M.comp T.dualCoannihilator.subtype)

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
end Lax342547.DuplicatedMoments
end

-- Lax342547.DuplicatedNoCover
section
namespace Lax342547.DuplicatedNoCover
end Lax342547.DuplicatedNoCover
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

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N Comp : Type} [Fintype B] [Fintype H] [Fintype N] [Fintype Comp]

variable [DecidableEq Comp]

noncomputable def uniformLaw (E : Matrix B B Binary) [Nonempty (Frame B H N E)] :
    PMF (Comp → Frame B H N E) := PMF.uniformOfFintype _

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

open Lax342547.MomentSpace Lax342547.RawFrames

open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def channels {E : Matrix B B Binary} (F : Frame B H N E) :
    Matrix N H Binary × Matrix N H Binary := (F.X, F.Y)

end Lax342547.ChannelDensity
end

-- Lax342547.ChannelColumns
section
namespace Lax342547.ChannelColumns

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters

open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters

open Lax342547.PushforwardWalsh Lax342547.RetainedImages

open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection

open scoped BigOperators

noncomputable def columnsEquiv {e N : Type} (h : ℕ) :
    (e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) ≃
      (e × Fin h → (N → Binary) × (N → Binary)) where
  toFun z := fun a => (fun i => (z a.1).1 i a.2,fun i => (z a.1).2 i a.2)
  invFun c := fun a => (fun i j => (c (a,j)).1 i,fun i j => (c (a,j)).2 i)
  left_inv _ := rfl
  right_inv _ := rfl

end Lax342547.ChannelColumns
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

-- Lax342547.MultiChannelPhase
section
namespace Lax342547.MultiChannelPhase

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters

open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters

open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns

open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection

open scoped BigOperators

axiom no_cover_marked_unit_phase {e d B N Ω U : Type} [Fintype e] [Fintype d] [Fintype B] [Fintype N] [Fintype Ω] [Fintype U]
    [DecidableEq e] [DecidableEq d] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (β : U → ℝ) (image : U → (e × d) → Frame B (Fin h) N E) (L : ℝ)
    (S : U → e → Matrix N N Binary)
    (hβ : Probability β) (hL : 0 ≤ L)
    (hβcap : ∀ o, push β image o ≤ L*weights (Lax342547.RawLaw.uniformLaw E) o)
    (hS : ∀ o, (∑ i, (S o i).rank) ≤ r)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    |∑ o, β o*(∑ x, μ x*ψ (S o) x*tensorCharacter h (fun i : e × d => A x i.1) (columnsEquiv h (fun a => channels (image o a))))| ≤
      θ+L*((r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*
        (2 : ℝ)^(Fintype.card (e × d)*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^((Fintype.card d*h)*2^(k-(100*r+12))))/θ^(2*t)))

end Lax342547.MultiChannelPhase
end
