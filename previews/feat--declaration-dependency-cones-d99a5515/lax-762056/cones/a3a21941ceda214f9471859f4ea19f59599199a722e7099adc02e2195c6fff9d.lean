-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax762056.ColumnGraph
section
namespace Lax762056.ColumnGraph.columnGraph
end Lax762056.ColumnGraph.columnGraph

namespace Lax762056.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

end Lax762056.ColumnGraph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax762056.GraphEncoding
section
namespace Lax762056
end Lax762056

namespace Lax762056.GraphEncoding
end Lax762056.GraphEncoding

namespace Lax762056.GraphEncoding.Instance
end Lax762056.GraphEncoding.Instance
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut
end Lax762056.MaxCut
end

-- Lax762056.Reduction
section
namespace Lax762056.Reduction.retainedVertices
end Lax762056.Reduction.retainedVertices

namespace Lax762056.Reduction

open ColumnGraph MaxCut

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

abbrev Row {n : ℕ} (F : SimpleGraph (Fin n)) := Edge F × Bool

abbrev Vertex {n : ℕ} (F : SimpleGraph (Fin n)) :=
  ColumnGraph.Vertex (Row F) (2 * n - 1)

end Lax762056.Reduction
end
