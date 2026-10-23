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

/-- A finite probability distribution over non-anticipative algorithms. -/
structure Randomized (R : Revelation P) where
  algorithms : List (ℚ × Algorithm P)
  nonneg : ∀ a ∈ algorithms, 0 ≤ a.1
  total : (algorithms.map Prod.fst).sum = 1
  nonAnticipative : ∀ a ∈ algorithms, NonAnticipative R a.2

/-- The expected cost of a randomized algorithm on an instance. -/
def Randomized.cost {R : Revelation P} (μ : Randomized R) (x : P.Inst) : ℚ :=
  (μ.algorithms.map fun a => a.1 * P.cost x (a.2 x)).sum

def Randomized.Competitive {R : Revelation P} (μ : Randomized R) (ρ α : ℚ) : Prop :=
  ∀ x, (∀ a ∈ μ.algorithms, P.feasible x (a.2 x)) ∧
    ∀ σ, P.feasible x σ → μ.cost x ≤ ρ * P.cost x σ + α

end Lax434175.Online
end
