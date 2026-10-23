-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat

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

-- Lax434175.Online
section
namespace Lax434175.Online.Causal
end Lax434175.Online.Causal

namespace Lax434175.Online.Hard
end Lax434175.Online.Hard

namespace Lax434175.Online.Randomized
end Lax434175.Online.Randomized

namespace Lax434175.Online.Revelation
end Lax434175.Online.Revelation

namespace Lax434175.Online

open Lax434175.Problems

variable {P : Problem}

/-- A deterministic algorithm: a schedule for every instance. -/
abbrev Algorithm (P : Problem) := (x : P.Inst) → P.Sched x

/-- The scheduler wins on every instance: a feasible schedule costing at most
`ρ` times every feasible schedule, plus `α`. -/
def Competitive (A : Algorithm P) (ρ α : ℚ) : Prop :=
  ∀ x, P.feasible x (A x) ∧ ∀ σ, P.feasible x σ → P.cost x (A x) ≤ ρ * P.cost x σ + α

end Lax434175.Online
end
