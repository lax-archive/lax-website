-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.DeriveFintype

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses
end

-- Lax228581.Treewidth
section
namespace Lax228581.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

/-- `G` has a tree decomposition all of whose bags have at most `w + 1`
vertices. -/
def HasTreewidthAtMost {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ w + 1

/-- The treewidth of a finite simple graph: the least `w` such that the
graph has a tree decomposition with bags of at most `w + 1` vertices. -/
noncomputable def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {w | HasTreewidthAtMost G w}

end Lax228581.Treewidth
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

open scoped Classical

open Lax228581.Treewidth

/-- A connected route for every edge, disjoint for nonincident edges. -/
structure AlmostEmbedding {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- Vertex images, with no injectivity requirement. -/
  vertexMap : Fin t → Fin n
  /-- Host vertices on each route. -/
  route : H.edgeSet → Finset (Fin n)
  /-- Each route is nonempty and connected. -/
  connected : ∀ e, (G.induce (↑(route e) : Set (Fin n))).Connected
  /-- A route contains the images of its edge's endpoints. -/
  endpoints : ∀ e v, v ∈ e.val → vertexMap v ∈ route e
  /-- Routes of nonincident edges share no host vertex. -/
  disjoint : ∀ e f, Disjoint e.val.toFinset f.val.toFinset → Disjoint (route e) (route f)

end Lax263307.AlmostEmbeddings
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

open scoped Classical

open AlmostEmbeddings

noncomputable def longEdges {t n : ℕ} {H : SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) (L : ℕ) : Finset (Sym2 (Fin t)) :=
  (Finset.univ.filter fun e : H.edgeSet => L < (E.route e).card).image Subtype.val

end Lax263307.RoutePruning
end

-- Lax263307.Entropy
section
namespace Lax263307.Entropy

/-- Entropy measured with natural logarithms. -/
noncomputable def naturalEntropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  ∑ v, Real.negMulLog (π v)

/-- Shannon entropy in bits. -/
noncomputable def entropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  naturalEntropy π / Real.log 2

/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end Lax263307.Entropy
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling

open Entropy (adjacencyMass edgeCost)

/-- Finite outcome probabilities and their associated vertex sets. -/
structure Distribution (n q : ℕ) where
  /-- Probability of each outcome. -/
  probability : Fin q → ℝ
  /-- Probabilities are nonnegative. -/
  nonnegative : ∀ i, 0 ≤ probability i
  /-- Total probability is one. -/
  normalized : (∑ i, probability i) = 1
  /-- The vertices used by each outcome. -/
  vertices : Fin q → Finset (Fin n)

/-- Probability of using a particular vertex. -/
noncomputable def load {n q : ℕ} (P : Distribution n q) (v : Fin n) : ℝ :=
  ∑ i, if v ∈ P.vertices i then P.probability i else 0

/-- Expected number of used vertices. -/
noncomputable def expectedSize {n q : ℕ} (P : Distribution n q) : ℝ :=
  ∑ i, P.probability i * ((P.vertices i).card : ℝ)

/-- Probability that independent outcomes have a common vertex. -/
noncomputable def collisionProbability {n q : ℕ} (P : Distribution n q) : ℝ :=
  ∑ i, ∑ j, if ¬Disjoint (P.vertices i) (P.vertices j) then
    P.probability i * P.probability j else 0

/-- Probability that a graph edge joins independent outcomes. -/
noncomputable def adjacencyProbability {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P : Distribution n q) : ℝ :=
  ∑ i, ∑ j, if ∃ u ∈ P.vertices i, ∃ v ∈ P.vertices j, G.Adj u v then
    P.probability i * P.probability j else 0

end Lax263307.PathSampling
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

open PathSampling (load)

open scoped NNReal NNRat

open RoutingNormalization VertexSplitting

open Lax455465.ConcurrentFlow

structure Distribution {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) where
  probability : Fin q → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  normalized : (∑ i, probability i) = 1
  route : Fin q → List (Fin n)
  valid : ∀ i, 0 < probability i → (route i).Nodup ∧ (route i).IsChain G.Adj ∧ route i ≠ []
  uniform : ∀ u v, (∑ i, if (route i).head? = some u ∧ (route i).getLast? = some v then
    probability i else 0) = 1 / (n : ℝ) ^ 2

noncomputable def Distribution.toSampling {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) : PathSampling.Distribution n q where
  probability := D.probability
  nonnegative := D.nonnegative
  normalized := D.normalized
  vertices i := (D.route i).toFinset

end Lax263307.RouteDistributions
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

open PathSampling (adjacencyProbability collisionProbability expectedSize)

open RouteDistributions (Distribution)

open RoutePruning (longEdges)

open AlmostEmbeddings InducedRouteEdges Lax228581.Treewidth

open GraphClasses

def HasBagBound (C : GraphClass) (W : ℕ → ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
    ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ W G.edgeSet.ncard

end Lax263307.InducedEmbeddingWidth
end

-- Lax263307.CostSamplingObstruction
section
namespace Lax263307.CostSamplingObstruction

open Entropy (edgeCost)

open PathSampling (load)

open RouteDistributions (Distribution)

open GraphClasses InducedEmbeddingWidth Lax228581.Treewidth

axiom cost_width_obstruction {t n q : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member : G ∈ C n) (D : Distribution G q) (hn : 0 < n)
    (d L : ℕ) (degree_bound : ∀ v, H.degree v ≤ d) (edge_positive : 0 < H.edgeSet.ncard)
    (x : Fin n → ℝ) (k ℓ p : ℝ) (k_positive : 0 < k) (ℓ_positive : 0 < ℓ) (p_positive : 0 < p)
    (cost_bounds : ∀ v, 0 ≤ x v ∧ x v ≤ 1) (mass : (∑ v, x v) ≤ k)
    (load_bound : ∀ v, load D.toSampling v ≤ ℓ * x v / k)
    (edge_bound : edgeCost G x ≤ k ^ 2 / p)
    (target_large : 8 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ k)
    (sparsity_large : 16 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ p) :
    ∃ removed : ℕ, (L : ℝ) * removed ≤ 4 * (H.edgeSet.ncard : ℝ) * ℓ ∧
      treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed

end Lax263307.CostSamplingObstruction
end
