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

def Residual {V : Type} (c f : V → V → ℝ) (a b : V) : Prop := f a b < c a b

end Lax342547.RealFlows
end

-- Lax342547.ResidualFlows
section
namespace Lax342547.ResidualFlows

open Lax342547.RealFlows

open scoped BigOperators Topology

open Filter

axiom maximal_no_residual_path {V : Type} [Fintype V]
    (c f : V → V → ℝ) (s t : V) (hst : s ≠ t) (hf : Feasible c f s t)
    (hmax : ∀ g, Feasible c g s t → divergence g s ≤ divergence f s) :
    ¬ Relation.ReflTransGen (Residual c f) s t

end Lax342547.ResidualFlows
end
