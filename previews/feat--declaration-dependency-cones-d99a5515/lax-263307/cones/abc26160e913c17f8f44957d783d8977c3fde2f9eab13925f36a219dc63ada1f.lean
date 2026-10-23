-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

end Lax263307.IndependentBlowUp
end
