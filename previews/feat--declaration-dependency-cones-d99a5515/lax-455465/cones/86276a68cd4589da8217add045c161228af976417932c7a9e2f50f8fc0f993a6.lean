-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count
import Mathlib.Data.NNReal.Basic

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

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

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
