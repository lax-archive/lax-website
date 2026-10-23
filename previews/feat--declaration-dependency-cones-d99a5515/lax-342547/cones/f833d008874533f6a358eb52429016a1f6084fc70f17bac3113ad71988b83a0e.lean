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
namespace Lax342547.RealFlows

open scoped BigOperators Topology

noncomputable def divergence {V : Type} [Fintype V] (f : V → V → ℝ) (a : V) : ℝ := ∑ b, f a b

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

axiom divergence_cut_sum {V : Type} [Fintype V] (f : V → V → ℝ) (Z : Finset V)
    (hskew : ∀ a b, f a b = -f b a) : by
    classical
    exact (∑ a ∈ Z, divergence f a) = ∑ a ∈ Z, ∑ b ∈ Zᶜ, f a b

end Lax342547.FlowCuts
end
