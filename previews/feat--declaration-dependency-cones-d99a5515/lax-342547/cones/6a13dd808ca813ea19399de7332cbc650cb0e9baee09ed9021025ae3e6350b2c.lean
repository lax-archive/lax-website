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

def left {A B : Type} (a : A) : Vertex A B := .inr (.inl a)

def right {A B : Type} (b : B) : Vertex A B := .inr (.inr b)

noncomputable def capacity {A B : Type} (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) :
    Vertex A B → Vertex A B → ℝ
  | .inl false, .inr (.inl x) => a x
  | .inr (.inl x), .inr (.inr y) => p x y
  | .inr (.inr y), .inl true => b y
  | _, _ => 0

axiom right_conservation {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (f : Vertex A B → Vertex A B → ℝ)
    (hf : Feasible (capacity a b p) f source sink) (y : B) :
    (∑ x, f (left x) (right y)) = f (right y) sink

end Lax342547.BipartiteFlows
end
