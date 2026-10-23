-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange

-- Lax222097.ColumnGraph
section
namespace Lax222097
end Lax222097

namespace Lax222097.ColumnGraph
end Lax222097.ColumnGraph

namespace Lax222097.ColumnGraph.columnGraph
end Lax222097.ColumnGraph.columnGraph
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
namespace Lax222097.Reduction.retainedVertices
end Lax222097.Reduction.retainedVertices

namespace Lax222097.Reduction

open ColumnGraph MaxCut

abbrev Edge {n : ℕ} (F : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ F.Adj e.1 e.2}

end Lax222097.Reduction
end
