-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

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

end Lax263307.PathSampling
end

-- Lax263307.RoutingNormalization
section
namespace Lax263307.RoutingNormalization

open scoped Classical

noncomputable def routed {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (u v : Fin n) : ℝ :=
  ∑ i, if E u v i then w i else 0

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

/-- Normalize finite graph routes commodity by commodity. -/
axiom finite_routes {n q : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (w : Fin q → ℝ) (E : Fin n → Fin n → Fin q → Prop)
    (w_nonnegative : ∀ i, 0 ≤ w i) (γ : ℝ) (γ_positive : 0 < γ)
    (lower : ∀ u v, 1 / γ ≤ routed w E u v)
    (Q : Fin q → List (Fin n))
    (routes : ∀ u v i, E u v i → (Q i).Nodup ∧ (Q i).IsChain G.Adj ∧
      (Q i).head? = some u ∧ (Q i).getLast? = some v) :
    ∃ D : Distribution G (n * (n * q)), ∀ z,
      load D.toSampling z ≤ γ / (n : ℝ) ^ 2 *
        (∑ i, w i * (if z ∈ Q i then (1 : ℝ) else 0))

end Lax263307.RouteDistributions
end
