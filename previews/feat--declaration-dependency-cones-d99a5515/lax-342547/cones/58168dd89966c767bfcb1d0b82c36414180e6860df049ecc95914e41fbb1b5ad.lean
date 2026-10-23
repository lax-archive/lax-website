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

def Residual {V : Type} (c f : V → V → ℝ) (a b : V) : Prop := f a b < c a b

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

def Direction {V : Type} [Fintype V] (c f d : V → V → ℝ) (u v : V) : Prop := by
  classical
  exact (∀ a b, d a b = -d b a) ∧
  (∀ a, divergence d a = (if a=u then 1 else 0)-(if a=v then 1 else 0)) ∧
  (∀ a b, ¬ Residual c f a b → d a b ≤ 0)

axiom edge_direction {V : Type} [Fintype V] (c f : V → V → ℝ) (u v : V)
    (huv : Residual c f u v) : Direction c f (edgeDirection u v) u v

end Lax342547.ResidualFlows
end
