-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat

-- Lax434175.Problems
section
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems

/-- A minimization problem. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The candidate solutions of an instance. -/
  Sched : Inst → Type
  /-- Which candidate solutions are feasible. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The cost of a candidate solution. -/
  cost : (x : Inst) → Sched x → ℚ

/-- The data of an embedding of `A` into `B`: a map on instances and
translations of solutions in both directions. -/
structure Embedding (A B : Problem) where
  map : A.Inst → B.Inst
  forth : (x : A.Inst) → A.Sched x → B.Sched (map x)
  back : (x : A.Inst) → B.Sched (map x) → A.Sched x

/-- An embedding is sound if both translations preserve feasibility and do
not increase the cost. -/
structure Embedding.Sound {A B : Problem} (e : Embedding A B) : Prop where
  forth_feasible : ∀ x σ, A.feasible x σ → B.feasible (e.map x) (e.forth x σ)
  forth_cost : ∀ x σ, A.feasible x σ → B.cost (e.map x) (e.forth x σ) ≤ A.cost x σ
  back_feasible : ∀ x τ, B.feasible (e.map x) τ → A.feasible x (e.back x τ)
  back_cost : ∀ x τ, B.feasible (e.map x) τ → A.cost x (e.back x τ) ≤ B.cost (e.map x) τ

/-- `A` is a special case of `B`. -/
def SpecialCase (A B : Problem) : Prop := ∃ e : Embedding A B, e.Sound

end Lax434175.Problems
end
