-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Instances.Real.Lemmas

-- Lax342547.RealFlows
section
namespace Lax342547.RealFlows

open scoped BigOperators Topology

def Residual {V : Type} (c f : V → V → ℝ) (a b : V) : Prop := f a b < c a b

end Lax342547.RealFlows
end
