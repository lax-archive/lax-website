-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax222097.ColumnGraph
section
namespace Lax222097.ColumnGraph.columnGraph
end Lax222097.ColumnGraph.columnGraph

namespace Lax222097.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

end Lax222097.ColumnGraph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax222097.GraphEncoding
section
namespace Lax222097
end Lax222097

namespace Lax222097.GraphEncoding
end Lax222097.GraphEncoding

namespace Lax222097.GraphEncoding.Instance
end Lax222097.GraphEncoding.Instance
end

-- Lax222097.MaxCut
section
namespace Lax222097.MaxCut
end Lax222097.MaxCut
end

-- Lax222097.Reduction
section
namespace Lax222097.Reduction

open ColumnGraph MaxCut

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

abbrev Row {n : ℕ} (F : SimpleGraph (Fin n)) := Edge F × Bool

abbrev Vertex {n : ℕ} (F : SimpleGraph (Fin n)) :=
  ColumnGraph.Vertex (Row F) (2 * n - 1)

def retainedVertices {n : ℕ} (F : SimpleGraph (Fin n)) : Set (Vertex F) :=
  fun ((edge, tag), column, side) =>
    let u := edge.val.1.val
    let v := edge.val.2.val
    let j := column.val
    (j = 2 * u ∧ side = tag) ∨
    (2 * u < j ∧ j < 2 * v) ∨
    (j = 2 * v ∧ side = !tag)

end Lax222097.Reduction
end
