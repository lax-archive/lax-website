-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents
end Lax263307.SeparatorComponents

namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding
end Lax263307.RecursiveRounding
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding
end Lax263307.ComponentCutEncoding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps
end Lax263307.StrongComponentGaps
end

-- Lax263307.HeavyRecursiveRounding
section
namespace Lax263307.HeavyRecursiveRounding

open LinearRelaxation SeparatorComponents

open ComponentCutEncoding

axiom ignored_cost {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (δ k : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (hk : 0 ≤ k) (count : Fintype.card ι ≤ 2 * n) :
    (∑ i, if δ * k / (4 * n) < c i then 0 else c i) ≤ δ * k / 2

end Lax263307.HeavyRecursiveRounding
end
