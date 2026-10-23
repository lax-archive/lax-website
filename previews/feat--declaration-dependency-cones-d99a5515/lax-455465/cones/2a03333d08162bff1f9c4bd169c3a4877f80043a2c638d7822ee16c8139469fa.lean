-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

-- Lax455465.ProductNetwork
section
open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- Whether capacities are shared by both directions of an edge or belong
to individual directed arcs. -/
inductive EdgeKind
  /-- One capacity shared by both directions of an undirected edge. -/
  | undirected
  /-- A separate capacity for each directed arc. -/
  | directed
  deriving DecidableEq

/-- A finite loopless network with nonnegative capacities. -/
structure Network (n : ℕ) where
  /-- The capacity of an edge or arc, with zero denoting absence. -/
  capacity : Fin n → Fin n → ℝ≥0
  /-- Loops are absent. -/
  loopless : ∀ v, capacity v v = 0

/-- An undirected network has the same capacity in both directions. -/
def Network.IsUndirected {n : ℕ} (N : Network n) : Prop :=
  ∀ u v, N.capacity u v = N.capacity v u

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

/-- The number of vertices with positive weight. -/
noncomputable def supportCount {n : ℕ} (π : VertexWeight n) : ℕ :=
  (Finset.univ.filter fun v => 0 < π v).card

/-- The total vertex weight in a set. -/
def mass {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ v ∈ S, π v

/-- A cut separates positive total weight on both sides. -/
def AdmissibleCut {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : Prop :=
  0 < mass π S ∧ 0 < mass π Sᶜ

/-- The capacity leaving a cut; symmetric capacities count an undirected
edge exactly once. -/
def cutCapacity {n : ℕ} (N : Network n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.capacity u v

/-- The ratio of cut capacity to separated product demand. -/
noncomputable def ratioCost {n : ℕ} (N : Network n) (π : VertexWeight n)
    (S : Finset (Fin n)) : ℝ≥0 :=
  cutCapacity N S / (mass π S * mass π Sᶜ)

/-- The least ratio cost of a cut with positive demand. -/
noncomputable def sparsestCut {n : ℕ} (N : Network n) (π : VertexWeight n) : ℝ≥0 :=
  sInf {r | ∃ S : Finset (Fin n), AdmissibleCut π S ∧ ratioCost N π S = r}

/-- The paper's base-two logarithm. -/
noncomputable def logFactor (p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log 2

end Lax455465.ProductNetwork
end

-- Lax455465.ConcurrentFlow
section
open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

/-- A finite assignment of nonnegative flow amounts to vertex lists. -/
abbrev PathFlow (n : ℕ) := List (Fin n) →₀ ℝ≥0

/-- Every path carrying positive flow is simple and has distinct endpoints. -/
def IsPathFlow {n : ℕ} (F : PathFlow n) : Prop :=
  ∀ P ∈ F.support, 2 ≤ P.length ∧ P.Nodup

/-- The forward load on an arc, counting its occurrences on each path. -/
noncomputable def arcLoad {n : ℕ} (F : PathFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support, F P * ((P.zip P.tail).count (u, v) : ℝ≥0)

/-- The capacity consumed by a path flow in the chosen edge model. -/
noncomputable def edgeLoad {n : ℕ} (kind : EdgeKind) (F : PathFlow n)
    (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => arcLoad F u v + arcLoad F v u
  | .directed => arcLoad F u v

/-- The amount routed from one endpoint to another. -/
noncomputable def routed {n : ℕ} (F : PathFlow n) (s t : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support,
    if P.head? = some s ∧ P.getLast? = some t then F P else 0

/-- The demand assigned to an ordered pair of distinct endpoints. -/
noncomputable def pairDemand {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (s t : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => π s * π t / 2
  | .directed => π s * π t

/-- A simple-path flow respects capacities and meets the specified common
fraction of every demand. -/
def IsConcurrentFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : PathFlow n) : Prop :=
  IsPathFlow F ∧
    (∀ u v, edgeLoad kind F u v ≤ N.capacity u v) ∧
      ∀ s t, s ≠ t → f * pairDemand kind π s t ≤ routed F s t

/-- The largest feasible concurrent-flow value, expressed as a supremum. -/
noncomputable def maxFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) : ℝ≥0 :=
  sSup {f | ∃ F : PathFlow n, IsConcurrentFlow kind N π f F}

end Lax455465.ConcurrentFlow
end

-- Lax455465.ArcToPath
section
namespace Lax455465.ArcToPath
end Lax455465.ArcToPath
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
namespace Lax455465.RationalEncoding.ArcCertificate
end Lax455465.RationalEncoding.ArcCertificate

namespace Lax455465.RationalEncoding.FlowCertificate
end Lax455465.RationalEncoding.FlowCertificate

namespace Lax455465.RationalEncoding.encodeInput
end Lax455465.RationalEncoding.encodeInput

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- A product instance with nonnegative rational capacities and weights. -/
structure RationalInstance (n : ℕ) where
  /-- The rational capacity of each edge or directed arc. -/
  capacity : Fin n → Fin n → ℚ≥0
  /-- Loops have zero capacity. -/
  loopless : ∀ v, capacity v v = 0
  /-- The rational weights specifying product demands. -/
  weight : Fin n → ℚ≥0

/-- Interpret rational capacities as exact nonnegative real capacities. -/
def RationalInstance.network {n : ℕ} (I : RationalInstance n) : Network n where
  capacity u v := (I.capacity u v : ℝ≥0)
  loopless v := by simpa using congrArg (fun q : ℚ≥0 => (q : ℝ≥0)) (I.loopless v)

/-- Interpret rational vertex weights as exact nonnegative real weights. -/
def RationalInstance.weights {n : ℕ} (I : RationalInstance n) : VertexWeight n :=
  fun v => (I.weight v : ℝ≥0)

end Lax455465.RationalEncoding
end

-- Lax455465.FlowCutCertificate
section
namespace Lax455465.FlowCutCertificate
end Lax455465.FlowCutCertificate

namespace Lax455465.FlowCutCertificate.Certificate
end Lax455465.FlowCutCertificate.Certificate
end

-- Lax455465.RamProductFlowCut
section
namespace Lax455465.RamProductFlowCut
end Lax455465.RamProductFlowCut
end

-- Lax455465.ProductFlowCut
section
namespace Lax455465.ProductFlowCut

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- The classical flow–cut inequality follows from the constructive certificate. -/
axiom exists_flow_cut_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
      (kind = .undirected → I.network.IsUndirected) →
      2 ≤ supportCount I.weights →
      (sparsestCut I.network I.weights : ℝ) ≤
        C * logFactor (supportCount I.weights) * (maxFlow kind I.network I.weights : ℝ)

end Lax455465.ProductFlowCut
end
