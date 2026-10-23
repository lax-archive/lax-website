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

/-- The forward load on an arc, counting its occurrences on each path. -/
noncomputable def arcLoad {n : ℕ} (F : PathFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support, F P * ((P.zip P.tail).count (u, v) : ℝ≥0)

/-- The capacity consumed by a path flow in the chosen edge model. -/
noncomputable def edgeLoad {n : ℕ} (kind : EdgeKind) (F : PathFlow n)
    (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => arcLoad F u v + arcLoad F v u
  | .directed => arcLoad F u v

/-- The demand assigned to an ordered pair of distinct endpoints. -/
noncomputable def pairDemand {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (s t : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => π s * π t / 2
  | .directed => π s * π t

/-- An arc flow records a nonnegative amount for each commodity and arc. -/
abbrev ArcFlow (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ≥0

/-- Aggregate forward capacity consumption in the edge formulation. -/
def totalArcLoad {n : ℕ} (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ s, ∑ t, F s t u v

/-- Shared or separate capacities in the edge formulation. -/
def totalEdgeLoad {n : ℕ} (kind : EdgeKind) (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => totalArcLoad F u v + totalArcLoad F v u
  | .directed => totalArcLoad F u v

/-- Net required supply at a vertex for one commodity; diagonal commodities
have zero supply at every vertex. -/
noncomputable def requiredSupply {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (f : ℝ≥0) (s t u : Fin n) : ℝ :=
  if s = t then 0 else
    (if u = s then (f * pairDemand kind π s t : ℝ≥0) else 0) -
    (if u = t then (f * pairDemand kind π s t : ℝ≥0) else 0)

/-- Capacity and exact commodity conservation in the polynomial-size arc formulation. -/
def IsArcConcurrentFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : ArcFlow n) : Prop :=
  (∀ u v, totalEdgeLoad kind F u v ≤ N.capacity u v) ∧
  ∀ s t u, (∑ v, (F s t u v : ℝ)) - (∑ v, (F s t v u : ℝ)) =
    requiredSupply kind π f s t u

end Lax455465.ConcurrentFlow
end
