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

def Feasible {V : Type} [Fintype V] (c f : V → V → ℝ) (s t : V) : Prop :=
  (∀ a b, f a b = -f b a) ∧ (∀ a b, f a b ≤ c a b) ∧
    (∀ a, a ≠ s → a ≠ t → divergence f a = 0)

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

axiom real_max_flow_min_cut {V : Type} [Fintype V] (c : V → V → ℝ) (s t : V)
    (hst : s ≠ t) (hc : ∀ a b, 0 ≤ c a b) :
    ∃ f Z, Feasible c f s t ∧ s ∈ Z ∧ t ∉ Z ∧ divergence f s = cutCapacity c Z ∧
      ∀ g, Feasible c g s t → divergence g s ≤ divergence f s

end Lax342547.FlowCuts
end
