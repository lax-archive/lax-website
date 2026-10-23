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

open Lax342547.RealFlows

open scoped BigOperators Topology

open Filter

noncomputable def edgeDirection {V : Type} (u v : V) (a b : V) : ℝ := by
  classical
  exact (if a=u ∧ b=v then 1 else 0) - (if a=v ∧ b=u then 1 else 0)

end Lax342547.ResidualFlows
end
