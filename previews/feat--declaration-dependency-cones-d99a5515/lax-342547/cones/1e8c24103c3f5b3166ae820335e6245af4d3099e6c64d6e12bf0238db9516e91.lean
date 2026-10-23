-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Field
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
end Lax342547.FlowCuts
end

-- Lax342547.BipartiteFlows
section
namespace Lax342547.BipartiteFlows.capacity
end Lax342547.BipartiteFlows.capacity

namespace Lax342547.BipartiteFlows

open Lax342547.RealFlows

open scoped BigOperators

def Law {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p ρ : A → B → ℝ) : Prop :=
  (∀ x y, 0 ≤ ρ x y) ∧ (∑ x, ∑ y, ρ x y) = 1 ∧
    (∀ x, (∑ y, ρ x y) ≤ a x) ∧ (∀ y, (∑ x, ρ x y) ≤ b y) ∧ (∀ x y, ρ x y ≤ p x y)

end Lax342547.BipartiteFlows
end
