-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Relation
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.RealFlows
section
namespace Lax342547
end Lax342547

namespace Lax342547.RealFlows
end Lax342547.RealFlows
end

-- Lax342547.ResidualFlows
section
namespace Lax342547.ResidualFlows
end Lax342547.ResidualFlows
end

-- Lax342547.FlowCuts
section
namespace Lax342547.FlowCuts

open Lax342547.RealFlows

open scoped BigOperators

noncomputable def cutCapacity {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : ℝ := by
  classical
  exact ∑ a ∈ Z, ∑ b ∈ Zᶜ, c a b

axiom cut_indicator {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : by
    classical
    exact cutCapacity c Z = ∑ a, ∑ b, if a ∈ Z ∧ b ∉ Z then c a b else 0

end Lax342547.FlowCuts
end
