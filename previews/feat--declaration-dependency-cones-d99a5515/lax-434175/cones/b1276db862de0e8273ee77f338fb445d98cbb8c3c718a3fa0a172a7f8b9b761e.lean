-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators

-- Lax434175.Problems
section
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound

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

end Lax434175.Problems
end

-- Lax434175.Rejection
section
namespace Lax434175.Rejection

open Lax434175.Problems

structure Inst where
  jobs : ℕ
  p : Fin jobs → ℕ
  /-- The rejection cost of a job. -/
  e : Fin jobs → ℕ
  budget : ℕ

structure Sched (x : Inst) where
  /-- The accepted jobs. -/
  accepted : Finset (Fin x.jobs)
  start : Fin x.jobs → ℕ

def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ := σ.start j + x.p j

/-- The rejected jobs respect the budget and the accepted jobs do not
overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  ∑ j ∈ Finset.univ \ σ.accepted, x.e j ≤ x.budget ∧
  ∀ i ∈ σ.accepted, ∀ j ∈ σ.accepted, i ≠ j →
    completion x σ i ≤ σ.start j ∨ completion x σ j ≤ σ.start i

/-- `1 | Σ_{j ∈ reject} e_j ≤ B | ΣC_j` -/
def problem : Problem where
  Inst := Inst
  Sched := Sched
  feasible := feasible
  cost x σ := ((∑ j ∈ σ.accepted, completion x σ j : ℕ) : ℚ)

end Lax434175.Rejection
end
