-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNReal.Basic

-- Lax455465.ProductNetwork
section
namespace Lax455465.ProductNetwork.EdgeKind
end Lax455465.ProductNetwork.EdgeKind

namespace Lax455465.ProductNetwork.EdgeKind.directed
end Lax455465.ProductNetwork.EdgeKind.directed

namespace Lax455465.ProductNetwork.EdgeKind.undirected
end Lax455465.ProductNetwork.EdgeKind.undirected

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- A finite loopless network with nonnegative capacities. -/
structure Network (n : ℕ) where
  /-- The capacity of an edge or arc, with zero denoting absence. -/
  capacity : Fin n → Fin n → ℝ≥0
  /-- Loops are absent. -/
  loopless : ∀ v, capacity v v = 0

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

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

end Lax455465.ProductNetwork
end
