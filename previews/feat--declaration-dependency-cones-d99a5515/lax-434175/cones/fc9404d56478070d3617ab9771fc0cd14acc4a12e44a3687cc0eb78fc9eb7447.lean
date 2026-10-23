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

end Lax434175.Problems
end

-- Lax434175.Online
section
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

/-- The scheduler wins on every instance: a feasible schedule costing at most
`ρ` times every feasible schedule, plus `α`. -/
def Competitive (A : Algorithm P) (ρ α : ℚ) : Prop :=
  ∀ x, P.feasible x (A x) ∧ ∀ σ, P.feasible x σ → P.cost x (A x) ≤ ρ * P.cost x σ + α

/-- The scheduler has a winning strategy. -/
def SchedulerWins (R : Revelation P) (ρ α : ℚ) : Prop :=
  ∃ A, NonAnticipative R A ∧ Competitive A ρ α

/-- The embedding respects what is revealed and what is decided. -/
structure Causal {A B : Problem} (RA : Revelation A) (RB : Revelation B)
    (e : Embedding A B) : Prop where
  same : ∀ x y t, RA.same x y t → RB.same (e.map x) (e.map y) t
  agree : ∀ x y τ τ' t, RB.agree (e.map x) (e.map y) τ τ' t →
    RA.agree x y (e.back x τ) (e.back y τ') t

axiom schedulerWins_of_embedding {A B : Problem} {RA : Revelation A} {RB : Revelation B}
    {e : Embedding A B} (he : e.Sound) (hc : Causal RA RB e) {ρ α : ℚ} (hρ : 0 ≤ ρ) :
    SchedulerWins RB ρ α → SchedulerWins RA ρ α

end Lax434175.Online
end
