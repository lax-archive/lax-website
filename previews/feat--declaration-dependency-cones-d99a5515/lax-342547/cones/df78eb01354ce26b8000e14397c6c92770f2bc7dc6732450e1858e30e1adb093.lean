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
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
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
end Lax342547.FiniteSampling
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
namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change

namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

abbrev Injection (I N : Type) [Fintype I] :=
  {A : Matrix N I Binary // Function.Injective A.mulVec}

def plus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.P F.X, by
    intro x y h
    have h' := F.plus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def minus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.Q F.Y, by
    intro x y h
    have h' := F.minus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

end Lax342547.FrameSymmetry
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

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a

end Pin

end Lax342547.ExactPins
end

-- Lax342547.ConditionalMinus
section
namespace Lax342547.ConditionalMinus
end Lax342547.ConditionalMinus
end

-- Lax342547.ProductImages
section
namespace Lax342547.ProductImages

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames

open scoped ENNReal

def jointMatrix {Draw I N : Type} (A : Draw → Matrix N I Binary) : Matrix N (Draw × I) Binary :=
  fun n j => A j.1 n j.2

end Lax342547.ProductImages
end

-- Lax342547.ProductMinusImages
section
namespace Lax342547.ProductMinusImages
end Lax342547.ProductMinusImages
end

-- Lax342547.ReferenceImages
section
namespace Lax342547.ReferenceImages
end Lax342547.ReferenceImages
end

-- Lax342547.ImageScale
section
namespace Lax342547.ImageScale
end Lax342547.ImageScale
end

-- Lax342547.ReferencePins
section
namespace Lax342547.ReferencePins

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

open Lax342547.ProductImages Lax342547.ExactPins

open scoped ENNReal

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def observationMatrix {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary :=
  if a.2 then jointMatrix (fun i => (plus (o i a.1)).val)
  else jointMatrix (fun i => (minus (o i a.1)).val)

def observation {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary) :=
  (observationMatrix o a).mulVecLin

end Lax342547.ReferencePins
end

-- Lax342547.ProjectedPins
section
namespace Lax342547.ProjectedPins

open Lax342547.MomentSpace Lax342547.ExactPins

def primalProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (B → Binary) where
  toFun v b := v (i, Sum.inl b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projected {Comp B H N : Type} (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (i : Fin 2) (a : Comp × Bool) : Submodule Binary (B → Binary) :=
  (P.space a).map (primalProjection i)

end Lax342547.ProjectedPins
end

-- Lax342547.TableSpaces
section
namespace Lax342547.TableSpaces

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

def primalEmbedding {B H : Type} (i : Fin 2) :
    (B → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim v (fun _ => 0) x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def channelProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (H → Binary) where
  toFun v h := v (i, Sum.inr h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def channelEmbedding {B H : Type} (i : Fin 2) :
    (H → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim (fun _ => 0) v x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def protectedChannel {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (a : Comp × Bool) :
    Submodule Binary (H → Binary) := (P.space a).map (channelProjection i)

def tableSpace {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i, primalProjection i v ∈ projected P i a}
  zero_mem' := fun i => (projected P i a).zero_mem
  add_mem' := fun hv hw i => (projected P i a).add_mem (hv i) (hw i)
  smul_mem' := fun c _ hv i => (projected P i a).smul_mem c (hv i)

def pinnedPrimal {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (a : Comp × Bool) :
    Submodule Binary (B → Binary) := (P.space a).comap (primalEmbedding i)

end Lax342547.TableSpaces
end

-- Lax342547.SmallTables
section
namespace Lax342547.SmallTables

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

structure Table (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) where
  forward : ∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary
  reverse : ∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary

def tableChannel (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    (H → Binary) →ₗ[Binary] tableSpace P a where
  toFun v := ⟨channelEmbedding i v, by
    intro j
    have hz : primalProjection j (channelEmbedding (B := B) i v) = 0 := by
      ext b
      simp [primalProjection, channelEmbedding]
    rw [hz]
    exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((channelEmbedding i).map_add v w)
  map_smul' c v := Subtype.ext ((channelEmbedding i).map_smul c v)

def tablePinnedPrimal (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a : Comp × Bool) (i : Fin 2) : pinnedPrimal P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, fun _j => ⟨primalEmbedding i v.val, v.property, rfl⟩⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def rowChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (i z : Fin 2) :
    pinnedPrimal P i a →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tablePinnedPrimal P a i d) (tableChannel Q b z (Pi.single h 1))
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

noncomputable def columnChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (z i : Fin 2) :
    pinnedPrimal Q i b →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tableChannel P a z (Pi.single h 1)) (tablePinnedPrimal Q b i d)
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

def Injecting {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q) : Prop :=
  ∀ e i z,
    Function.Injective (((protectedChannel Q z (e, true)).mkQ).comp
      (rowChannels P Q (e, true) (e, false) (T.forward e) i z)) ∧
    Function.Injective (((protectedChannel Q z (e, false)).mkQ).comp
      (columnChannels Q P (e, true) (e, false) (T.reverse e) z i)) ∧
    Function.Injective (((protectedChannel P z (e, true)).mkQ).comp
      (rowChannels Q P (e, true) (e, false) (T.reverse e) i z)) ∧
    Function.Injective (((protectedChannel P z (e, false)).mkQ).comp
      (columnChannels P Q (e, true) (e, false) (T.forward e) z i))

variable [Fintype N] {ΩA ΩB : Type}

end Lax342547.SmallTables
end

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm
end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry
end Lax342547.TagGeometry

namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry
end Lax342547.ConcreteGeometry

namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ
end

-- Lax342547.TensorContractions
section
namespace Lax342547.TensorContractions
end Lax342547.TensorContractions
end

-- Lax342547.TableContractions
section
namespace Lax342547.TableContractions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables

structure CrossForms (Comp B H : Type) where
  forward : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)
  reverse : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)

end Lax342547.TableContractions
end

-- Lax342547.RawContractions
section
namespace Lax342547.RawContractions

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions

open Lax342547.ReferencePins

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N] {E : Matrix B B Binary}

def rawForms (oA oB : Fin 2 → Comp → Frame B H N E) : CrossForms Comp B H :=
  ⟨fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oA (e, true))
      (observation oB (e, false)),
    fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oB (e, true))
      (observation oA (e, false))⟩

end Lax342547.RawContractions
end

-- Lax342547.TableInjection
section
namespace Lax342547.TableInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins

open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions

open Lax342547.RawContractions Lax342547.FiniteInjection

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
  {E : Matrix B B Binary}

def rawTable (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) : Table P Q where
  forward e := ((rawForms A Bmap).forward e).compl₁₂
    (tableSpace P (e, true)).subtype (tableSpace Q (e, false)).subtype
  reverse e := ((rawForms A Bmap).reverse e).compl₁₂
    (tableSpace Q (e, true)).subtype (tableSpace P (e, false)).subtype

def primalMatrix (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2)
    (s : Bool) : Matrix N B Binary := if s then (A i e).P else (A i e).Q

def oppositeChannel (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2)
    (s : Bool) : Matrix N H Binary := if s then (A i e).Y else (A i e).X

def primalImage (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2) (s : Bool) :
    Submodule Binary (N → Binary) :=
  (pinnedPrimal P i (e, s)).map (primalMatrix A e i s).mulVecLin

def Failed (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2)
    (s role : Bool) : Prop :=
  if role then
    pinFailure (primalImage Q Bmap e i s) (oppositeChannel A e z s)
      (protectedChannel P z (e, s))
  else
    pinFailure (primalImage P A e i s) (oppositeChannel Bmap e z s)
      (protectedChannel Q z (e, s))

axiom actual_table_injecting_iff (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) :
    Injecting (rawTable P Q A Bmap) ↔ ∀ e i z s role,¬ Failed P Q A Bmap e i z s role

end Lax342547.TableInjection
end
