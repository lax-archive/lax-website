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

open Lax342547.RealFlows

open scoped BigOperators

noncomputable def cutCapacity {V : Type} [Fintype V] (c : V → V → ℝ) (Z : Finset V) : ℝ := by
  classical
  exact ∑ a ∈ Z, ∑ b ∈ Zᶜ, c a b

end Lax342547.FlowCuts
end

-- Lax342547.BipartiteFlows
section
namespace Lax342547.BipartiteFlows

open Lax342547.RealFlows

open scoped BigOperators

abbrev Vertex (A B : Type) := Bool ⊕ (A ⊕ B)

def source {A B : Type} : Vertex A B := .inl false

def sink {A B : Type} : Vertex A B := .inl true

noncomputable def capacity {A B : Type} (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) :
    Vertex A B → Vertex A B → ℝ
  | .inl false, .inr (.inl x) => a x
  | .inr (.inl x), .inr (.inr y) => p x y
  | .inr (.inr y), .inl true => b y
  | _, _ => 0

def Law {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p ρ : A → B → ℝ) : Prop :=
  (∀ x y, 0 ≤ ρ x y) ∧ (∑ x, ∑ y, ρ x y) = 1 ∧
    (∀ x, (∑ y, ρ x y) ≤ a x) ∧ (∀ y, (∑ x, ρ x y) ≤ b y) ∧ (∀ x y, ρ x y ≤ p x y)

axiom infeasible_cut {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hp : ∀ x y, 0 ≤ p x y)
    (hn : ¬ ∃ ρ, Law a b p ρ) :
    ∃ Z : Finset (Vertex A B), source ∈ Z ∧ sink ∉ Z ∧
      Lax342547.FlowCuts.cutCapacity (capacity a b p) Z < 1

end Lax342547.BipartiteFlows
end
