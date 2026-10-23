-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sublists
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.DeriveFintype

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.ExhaustiveTargets
section
namespace Lax263307.ExhaustiveTargets.search_correct
end Lax263307.ExhaustiveTargets.search_correct

namespace Lax263307.ExhaustiveTargets

/-- Enumerate the vertex sets of one prescribed cardinality. -/
def candidates (n k : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen k).map List.toFinset

/-- Deterministic exact search at target `k`. -/
def findIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Option (Finset (Fin n)) :=
  (candidates n k).find? fun I => decide (G.IsIndepSet (I : Set (Fin n)))

end Lax263307.ExhaustiveTargets
end

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ConditioningDistribution
section
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
end

-- Lax263307.Entropy
section
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
end Lax263307.Entropy
end

-- Lax263307.EntropyBounds
section
namespace Lax263307.EntropyBounds
end Lax263307.EntropyBounds
end

-- Lax263307.EntropyGap
section
namespace Lax263307.EntropyGap
end Lax263307.EntropyGap
end

-- Lax263307.HeavyConditioning
section
namespace Lax263307.HeavyConditioning
end Lax263307.HeavyConditioning
end

-- Lax109476.LinearProgram
section
namespace Lax109476
end Lax109476

namespace Lax109476.LinearProgram
end Lax109476.LinearProgram

namespace Lax109476.LinearProgram.Program
end Lax109476.LinearProgram.Program
end

-- Lax109476.FarkasCertificate
section
namespace Lax109476.FarkasCertificate
end Lax109476.FarkasCertificate
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection
end Lax109476.RecessionDirection
end

-- Lax109476.RationalCertificates
section
namespace Lax109476.RationalCertificates
end Lax109476.RationalCertificates

namespace Lax109476.RationalCertificates.Certificate
end Lax109476.RationalCertificates.Certificate

namespace Lax109476.RationalCertificates.IsValidCertificate
end Lax109476.RationalCertificates.IsValidCertificate

namespace Lax109476.RationalCertificates.Certificate.infeasible
end Lax109476.RationalCertificates.Certificate.infeasible

namespace Lax109476.RationalCertificates.Certificate.optimal
end Lax109476.RationalCertificates.Certificate.optimal

namespace Lax109476.RationalCertificates.Certificate.unbounded
end Lax109476.RationalCertificates.Certificate.unbounded
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding
end Lax263307.ComponentCutEncoding
end

-- Lax263307.RationalConditioning
section
namespace Lax263307.RationalConditioning
end Lax263307.RationalConditioning
end

-- Lax263307.CoordinateCatalog
section
namespace Lax263307.CoordinateCatalog
end Lax263307.CoordinateCatalog
end

-- Lax263307.MomentLP
section
namespace Lax263307.MomentLP
end Lax263307.MomentLP
end

-- Lax759944.BinaryWordEncoding
section
namespace Lax759944
end Lax759944

namespace Lax759944.BinaryWordEncoding
end Lax759944.BinaryWordEncoding

namespace Lax759944.BinaryWordEncoding.Symbol
end Lax759944.BinaryWordEncoding.Symbol

namespace Lax759944.BinaryWordEncoding.Symbol.one
end Lax759944.BinaryWordEncoding.Symbol.one

namespace Lax759944.BinaryWordEncoding.Symbol.separator
end Lax759944.BinaryWordEncoding.Symbol.separator

namespace Lax759944.BinaryWordEncoding.Symbol.zero
end Lax759944.BinaryWordEncoding.Symbol.zero
end

-- Lax808846.Ram
section
namespace Lax808846
end Lax808846

namespace Lax808846.Ram
end Lax808846.Ram

namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.State
end Lax808846.Ram.State

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime
end Lax759944.RamPolytime
end

-- Lax109476.RationalEncoding
section
namespace Lax109476.RationalEncoding
end Lax109476.RationalEncoding

namespace Lax109476.RationalEncoding.encodeCertificate
end Lax109476.RationalEncoding.encodeCertificate
end

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307
end Lax263307

namespace Lax263307.BufferedEllipsoid
end Lax263307.BufferedEllipsoid
end

-- Lax263307.RoundedOracleSearch
section
namespace Lax263307.RoundedOracleSearch
end Lax263307.RoundedOracleSearch

namespace Lax263307.RoundedOracleSearch.Reply
end Lax263307.RoundedOracleSearch.Reply

namespace Lax263307.RoundedOracleSearch.scan
end Lax263307.RoundedOracleSearch.scan

namespace Lax263307.RoundedOracleSearch.selectedNormal
end Lax263307.RoundedOracleSearch.selectedNormal

namespace Lax263307.RoundedOracleSearch.trajectory
end Lax263307.RoundedOracleSearch.trajectory

namespace Lax263307.RoundedOracleSearch.Reply.cut
end Lax263307.RoundedOracleSearch.Reply.cut

namespace Lax263307.RoundedOracleSearch.Reply.found
end Lax263307.RoundedOracleSearch.Reply.found

namespace Lax263307.RoundedOracleSearch.Reply.reject
end Lax263307.RoundedOracleSearch.Reply.reject
end

-- Lax263307.AlgorithmParameters
section
namespace Lax263307.AlgorithmParameters
end Lax263307.AlgorithmParameters
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents
end Lax263307.SeparatorComponents

namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding
end Lax263307.RecursiveRounding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps
end Lax263307.StrongComponentGaps
end

-- Lax263307.HeavyRecursiveRounding
section
namespace Lax263307.HeavyRecursiveRounding
end Lax263307.HeavyRecursiveRounding
end

-- Lax263307.ComputedRounding
section
namespace Lax263307.ComputedRounding
end Lax263307.ComputedRounding

namespace Lax263307.ComputedRounding.Result
end Lax263307.ComputedRounding.Result

namespace Lax263307.ComputedRounding.collect
end Lax263307.ComputedRounding.collect

namespace Lax263307.ComputedRounding.collect_correct
end Lax263307.ComputedRounding.collect_correct

namespace Lax263307.ComputedRounding.Result.cut
end Lax263307.ComputedRounding.Result.cut

namespace Lax263307.ComputedRounding.Result.found
end Lax263307.ComputedRounding.Result.found
end

-- Lax263307.GraphClasses
section
namespace Lax263307
end Lax263307

namespace Lax263307.GraphClasses
end Lax263307.GraphClasses
end

-- Lax263307.EdgeSublinearSeparators
section
namespace Lax263307.EdgeSublinearSeparators
end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.BalancedPartitions
section
namespace Lax263307.BalancedPartitions
end Lax263307.BalancedPartitions
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling
end Lax263307.PathSampling

namespace Lax263307.PathSampling.Distribution
end Lax263307.PathSampling.Distribution
end

-- Lax263307.RepeatedCutAccounting
section
namespace Lax263307.RepeatedCutAccounting
end Lax263307.RepeatedCutAccounting
end

-- Lax263307.CutTraces
section
namespace Lax263307.CutTraces
end Lax263307.CutTraces

namespace Lax263307.CutTraces.Trace
end Lax263307.CutTraces.Trace

namespace Lax263307.CutTraces.parts
end Lax263307.CutTraces.parts
end

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax263307.ConnectedBags
section
namespace Lax263307
end Lax263307

namespace Lax263307.ConnectedBags
end Lax263307.ConnectedBags
end

-- Lax263307.ConnectedRepresentations
section
namespace Lax263307.ConnectedRepresentations
end Lax263307.ConnectedRepresentations

namespace Lax263307.ConnectedRepresentations.Representation
end Lax263307.ConnectedRepresentations.Representation
end

-- Lax263307.AlmostEmbeddings
section
namespace Lax263307.AlmostEmbeddings
end Lax263307.AlmostEmbeddings

namespace Lax263307.AlmostEmbeddings.AlmostEmbedding
end Lax263307.AlmostEmbeddings.AlmostEmbedding
end

-- Lax263307.InducedRouteEdges
section
namespace Lax263307.InducedRouteEdges
end Lax263307.InducedRouteEdges
end

-- Lax263307.HostRestriction
section
namespace Lax263307.HostRestriction
end Lax263307.HostRestriction
end

-- Lax263307.IsolatedEmbeddingTransfer
section
namespace Lax263307.IsolatedEmbeddingTransfer
end Lax263307.IsolatedEmbeddingTransfer
end

-- Lax263307.EdgeDeletionWidth
section
namespace Lax263307
end Lax263307

namespace Lax263307.EdgeDeletionWidth
end Lax263307.EdgeDeletionWidth
end

-- Lax263307.RoutePruning
section
namespace Lax263307.RoutePruning
end Lax263307.RoutePruning
end

-- Lax263307.RoutingNormalization
section
namespace Lax263307.RoutingNormalization
end Lax263307.RoutingNormalization
end

-- Lax455465.ProductNetwork
section
namespace Lax455465
end Lax455465

namespace Lax455465.ProductNetwork
end Lax455465.ProductNetwork

namespace Lax455465.ProductNetwork.EdgeKind
end Lax455465.ProductNetwork.EdgeKind

namespace Lax455465.ProductNetwork.Network
end Lax455465.ProductNetwork.Network

namespace Lax455465.ProductNetwork.EdgeKind.directed
end Lax455465.ProductNetwork.EdgeKind.directed

namespace Lax455465.ProductNetwork.EdgeKind.undirected
end Lax455465.ProductNetwork.EdgeKind.undirected
end

-- Lax455465.ConcurrentFlow
section
namespace Lax455465.ConcurrentFlow
end Lax455465.ConcurrentFlow

namespace Lax455465.ConcurrentFlow.edgeLoad
end Lax455465.ConcurrentFlow.edgeLoad
end

-- Lax455465.RationalEncoding
section
namespace Lax455465.RationalEncoding
end Lax455465.RationalEncoding

namespace Lax455465.RationalEncoding.ArcCertificate
end Lax455465.RationalEncoding.ArcCertificate

namespace Lax455465.RationalEncoding.FlowCertificate
end Lax455465.RationalEncoding.FlowCertificate

namespace Lax455465.RationalEncoding.RationalInstance
end Lax455465.RationalEncoding.RationalInstance

namespace Lax455465.RationalEncoding.encodeInput
end Lax455465.RationalEncoding.encodeInput
end

-- Lax455465.FlowCutCertificate
section
namespace Lax455465.FlowCutCertificate
end Lax455465.FlowCutCertificate

namespace Lax455465.FlowCutCertificate.Certificate
end Lax455465.FlowCutCertificate.Certificate
end

-- Lax455465.RamDirectedUniformFlowCut
section
namespace Lax455465.RamDirectedUniformFlowCut
end Lax455465.RamDirectedUniformFlowCut
end

-- Lax263307.VertexSplitting
section
namespace Lax263307
end Lax263307

namespace Lax263307.VertexSplitting
end Lax263307.VertexSplitting
end

-- Lax263307.SplitPathProjection
section
namespace Lax263307.SplitPathProjection
end Lax263307.SplitPathProjection
end

-- Lax263307.RouteDistributions
section
namespace Lax263307.RouteDistributions
end Lax263307.RouteDistributions

namespace Lax263307.RouteDistributions.Distribution
end Lax263307.RouteDistributions.Distribution
end

-- Lax263307.ConditionalRoutes
section
namespace Lax263307.ConditionalRoutes
end Lax263307.ConditionalRoutes
end

-- Lax263307.FiniteProductSampling
section
namespace Lax263307.FiniteProductSampling
end Lax263307.FiniteProductSampling
end

-- Lax263307.CoupledRouteSampling
section
namespace Lax263307.CoupledRouteSampling
end Lax263307.CoupledRouteSampling
end

-- Lax263307.SamplingOutcomes
section
namespace Lax263307.SamplingOutcomes
end Lax263307.SamplingOutcomes
end

-- Lax263307.CoupledSamplingBounds
section
namespace Lax263307.CoupledSamplingBounds
end Lax263307.CoupledSamplingBounds
end

-- Lax263307.SampledAlmostEmbeddings
section
namespace Lax263307.SampledAlmostEmbeddings
end Lax263307.SampledAlmostEmbeddings
end

-- Lax263307.InducedEmbeddingWidth
section
namespace Lax263307.InducedEmbeddingWidth
end Lax263307.InducedEmbeddingWidth
end

-- Lax263307.PowerBagBounds
section
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet
end

-- Lax263307.RecursionDepth
section
namespace Lax263307.RecursionDepth

open WeightedIndependentSet (IsApproximation)

/-- Number of balanced reductions needed to reach order at most one. -/
def depth (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else 1 + depth (2 * n / 3)
termination_by n
decreasing_by omega

end Lax263307.RecursionDepth
end

-- Lax263307.SeparatorDecompositions
section
namespace Lax263307.SeparatorDecompositions
end Lax263307.SeparatorDecompositions
end

-- Lax263307.EdgeBagBounds
section
namespace Lax263307.EdgeBagBounds
end Lax263307.EdgeBagBounds
end

-- Lax263307.CostSamplingObstruction
section
namespace Lax263307.CostSamplingObstruction
end Lax263307.CostSamplingObstruction
end

-- Lax920634.EdgeExpansion
section
namespace Lax920634
end Lax920634

namespace Lax920634.EdgeExpansion
end Lax920634.EdgeExpansion
end

-- Lax920634.SeedSearch
section
namespace Lax920634
end Lax920634

namespace Lax920634.SeedSearch
end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation
end Lax920634.SeedRotation

namespace Lax920634.SeedRotation.lazyRotation
end Lax920634.SeedRotation.lazyRotation

namespace Lax920634.SeedRotation.walkAt
end Lax920634.SeedRotation.walkAt

namespace Lax920634.SeedRotation.walkEnd
end Lax920634.SeedRotation.walkEnd
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction
end Lax920634.ZigZagConstruction

namespace Lax920634.ZigZagConstruction.rotation
end Lax920634.ZigZagConstruction.rotation
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding
end Lax920634.GraphEncoding

namespace Lax920634.GraphEncoding.levelAfter
end Lax920634.GraphEncoding.levelAfter
end

-- Lax920634.ConstructionSize
section
namespace Lax920634.ConstructionSize
end Lax920634.ConstructionSize
end

-- Lax920634.ExplicitTreewidth
section
namespace Lax920634.ExplicitTreewidth
end Lax920634.ExplicitTreewidth
end

-- Lax920634.SubcubicConstruction
section
namespace Lax920634.SubcubicConstruction
end Lax920634.SubcubicConstruction
end

-- Lax263307.SourceGraphs
section
namespace Lax263307
end Lax263307

namespace Lax263307.SourceGraphs
end Lax263307.SourceGraphs
end

-- Lax263307.WidthGrowth
section
namespace Lax263307
end Lax263307

namespace Lax263307.WidthGrowth
end Lax263307.WidthGrowth
end

-- Lax263307.NoBoundedLoadRoutes
section
namespace Lax263307.NoBoundedLoadRoutes
end Lax263307.NoBoundedLoadRoutes
end

-- Lax263307.ForcedSeparation
section
namespace Lax263307.ForcedSeparation
end Lax263307.ForcedSeparation
end

-- Lax263307.ComputedSeparators
section
namespace Lax263307.ComputedSeparators
end Lax263307.ComputedSeparators

namespace Lax263307.ComputedSeparators.cuts
end Lax263307.ComputedSeparators.cuts

namespace Lax263307.ComputedSeparators.pieces
end Lax263307.ComputedSeparators.pieces
end

-- Lax263307.HeavyRationalConditioning
section
namespace Lax263307.HeavyRationalConditioning
end Lax263307.HeavyRationalConditioning
end

-- Lax263307.NearOracle
section
namespace Lax263307.NearOracle
end Lax263307.NearOracle

namespace Lax263307.NearOracle.ChildCorrect
end Lax263307.NearOracle.ChildCorrect

namespace Lax263307.NearOracle.Correct
end Lax263307.NearOracle.Correct

namespace Lax263307.NearOracle.Result
end Lax263307.NearOracle.Result

namespace Lax263307.NearOracle.run
end Lax263307.NearOracle.run

namespace Lax263307.NearOracle.Result.cut
end Lax263307.NearOracle.Result.cut

namespace Lax263307.NearOracle.Result.found
end Lax263307.NearOracle.Result.found

namespace Lax263307.NearOracle.Result.reject
end Lax263307.NearOracle.Result.reject
end

-- Lax263307.RationalCutBuffer
section
namespace Lax263307.RationalCutBuffer
end Lax263307.RationalCutBuffer
end

-- Lax109476.CertificateSoundness
section
namespace Lax109476.CertificateSoundness
end Lax109476.CertificateSoundness
end

-- Lax263307.DistanceProjection
section
namespace Lax263307
end Lax263307

namespace Lax263307.DistanceProjection
end Lax263307.DistanceProjection
end

-- Lax263307.RationalProjection
section
namespace Lax263307.RationalProjection
end Lax263307.RationalProjection

namespace Lax263307.RationalProjection.Correct
end Lax263307.RationalProjection.Correct

namespace Lax263307.RationalProjection.Outcome
end Lax263307.RationalProjection.Outcome

namespace Lax263307.RationalProjection.classify
end Lax263307.RationalProjection.classify

namespace Lax263307.RationalProjection.Outcome.far
end Lax263307.RationalProjection.Outcome.far

namespace Lax263307.RationalProjection.Outcome.near
end Lax263307.RationalProjection.Outcome.near

namespace Lax263307.RationalProjection.Outcome.reject
end Lax263307.RationalProjection.Outcome.reject
end

-- Lax109476.PolynomialTimeSolver
section
namespace Lax109476.PolynomialTimeSolver
end Lax109476.PolynomialTimeSolver
end

-- Lax263307.RegisteredLP
section
namespace Lax263307
end Lax263307

namespace Lax263307.RegisteredLP
end Lax263307.RegisteredLP

namespace Lax263307.RegisteredLP.parse
end Lax263307.RegisteredLP.parse

namespace Lax263307.RegisteredLP.rational
end Lax263307.RegisteredLP.rational

namespace Lax263307.RegisteredLP.vector
end Lax263307.RegisteredLP.vector
end

-- Lax263307.ProjectedOracle
section
namespace Lax263307.ProjectedOracle
end Lax263307.ProjectedOracle

namespace Lax263307.ProjectedOracle.Correct
end Lax263307.ProjectedOracle.Correct

namespace Lax263307.ProjectedOracle.SearchCorrect
end Lax263307.ProjectedOracle.SearchCorrect

namespace Lax263307.ProjectedOracle.run
end Lax263307.ProjectedOracle.run
end

-- Lax263307.TargetSearch
section
namespace Lax263307.TargetSearch
end Lax263307.TargetSearch

namespace Lax263307.TargetSearch.search
end Lax263307.TargetSearch.search
end

-- Lax263307.RecursiveAlgorithm
section
namespace Lax263307.RecursiveAlgorithm.Correct
end Lax263307.RecursiveAlgorithm.Correct

namespace Lax263307.RecursiveAlgorithm.attempt
end Lax263307.RecursiveAlgorithm.attempt

namespace Lax263307.RecursiveAlgorithm

open ExhaustiveTargets (findIndependentSet)

open RecursionDepth (depth)

open ComputedSeparators AlgorithmParameters

def accuracyDenominator (n : ℕ) (ε : ℚ) : ℕ :=
  4 * (depth n + 1) * ⌈ε⁻¹⌉₊

end Lax263307.RecursiveAlgorithm
end
