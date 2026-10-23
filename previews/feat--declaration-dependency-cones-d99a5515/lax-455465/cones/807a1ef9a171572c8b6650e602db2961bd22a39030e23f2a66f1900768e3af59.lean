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

namespace Lax455465.ProductNetwork.Network
end Lax455465.ProductNetwork.Network

namespace Lax455465.ProductNetwork.EdgeKind.directed
end Lax455465.ProductNetwork.EdgeKind.directed

namespace Lax455465.ProductNetwork.EdgeKind.undirected
end Lax455465.ProductNetwork.EdgeKind.undirected

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

end Lax455465.ProductNetwork
end
