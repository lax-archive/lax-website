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

namespace Lax434175.Online

open Lax434175.Problems

/-- How the instances of a problem are revealed over time. -/
structure Revelation (P : Problem) where
  /-- The two instances look the same to the scheduler at time `t`. -/
  same : P.Inst → P.Inst → NNRat → Prop
  /-- Two schedules of two instances made the same decisions up to time `t`. -/
  agree : (x y : P.Inst) → P.Sched x → P.Sched y → NNRat → Prop

variable {P : Problem}

/-- A deterministic algorithm: a schedule for every instance. -/
abbrev Algorithm (P : Problem) := (x : P.Inst) → P.Sched x

/-- The algorithm decides up to time `t` only from what is revealed at `t`. -/
def NonAnticipative (R : Revelation P) (A : Algorithm P) : Prop :=
  ∀ x y t, R.same x y t → R.agree x y (A x) (A y) t

/-- The adversary beats every non-anticipative algorithm. -/
def AdversaryWins (R : Revelation P) (ρ α : ℚ) : Prop :=
  ∀ A, NonAnticipative R A → ∃ x, ¬ P.feasible x (A x) ∨
    ∃ σ, P.feasible x σ ∧ ρ * P.cost x σ + α < P.cost x (A x)

end Lax434175.Online
end
