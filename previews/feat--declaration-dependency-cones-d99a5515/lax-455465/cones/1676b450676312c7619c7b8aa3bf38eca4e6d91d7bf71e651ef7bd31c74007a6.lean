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

/-- An undirected network has the same capacity in both directions. -/
def Network.IsUndirected {n : ℕ} (N : Network n) : Prop :=
  ∀ u v, N.capacity u v = N.capacity v u

end Lax455465.ProductNetwork
end
