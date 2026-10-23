-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators

-- Lax434175.Problems
section
namespace Lax434175
end Lax434175

namespace Lax434175.Problems
end Lax434175.Problems

namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

namespace Lax434175.Problems.Problem
end Lax434175.Problems.Problem

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound
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

end Lax434175.Rejection
end
