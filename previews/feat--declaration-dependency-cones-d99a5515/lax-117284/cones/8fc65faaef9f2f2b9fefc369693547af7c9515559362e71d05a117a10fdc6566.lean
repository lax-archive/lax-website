-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
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

-- Lax117284.ConflictGraph
section
namespace Lax117284.ConflictGraph
end Lax117284.ConflictGraph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.MulticolouredIndepSet
section
namespace Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime

/-- An instance of Multicoloured Independent Set: a graph on `colours` classes of `size`
vertices whose edges join vertices of different classes. -/
structure Instance where
  /-- The number `ℓ` of colour classes. -/
  colours : ℕ
  /-- The number `n` of vertices in each class. -/
  size : ℕ
  /-- The graph, on the vertices `(class, index)`. -/
  graph : SimpleGraph (Fin colours × Fin size)
  /-- Adjacent vertices lie in different classes. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → u.1 ≠ v.1

namespace Instance

variable (G : Instance)

end Instance

end Lax117284.MulticolouredIndepSet
end

-- Lax117284.Lemma14
section
namespace Lax117284.Lemma14

open Lax117284.Problems Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime Lax429075.Reductions

variable (G : Instance)

/-- The number of the vertex client of the vertex numbered `w`. -/
def vtxId (w : ℕ) : ℕ := 3 + G.colours + w

end Lax117284.Lemma14
end
