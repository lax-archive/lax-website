-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Finset.Lattice.Fold

-- Lax888481.Scheduling
section
namespace Lax888481.Scheduling

/-- An instance of interval scheduling with eligible machine sets: `jobs` jobs on
`machines` machines, each job with a processing time, a deadline, a weight, and the set
of machines allowed to run it. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The deadline `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ
  /-- The machines eligible to run job `j`. -/
  eligible : Fin jobs → Finset (Fin machines)
  /-- Every job takes at least one time unit. -/
  p_pos : ∀ j, 0 < p j
  /-- Every job fits before its deadline. -/
  p_le_d : ∀ j, p j ≤ d j

namespace Instance

variable (I : Instance)

/-- The time at which job `j` starts, namely `d j - p j`: a job occupies exactly the
interval `[d j - p j, d j)`. -/
def start (j : Fin I.jobs) : ℕ := I.d j - I.p j

variable {I}

variable (I)

end Instance

end Lax888481.Scheduling
end

-- Lax888481.DynamicProgram
section
namespace Lax888481.DynamicProgram

open Lax888481.Scheduling Lax888481.Scheduling.Instance

variable (I : Instance)

/-- A snapshot of the machines at one instant: which job, if any, occupies each. -/
abbrev State : Type := Fin I.machines → Option (Fin I.jobs)

variable {I}

/-- Job `j` is running at time `t`, that is `t ∈ [d j - p j, d j)`. -/
def Active (t : ℕ) (j : Fin I.jobs) : Prop := I.start j ≤ t ∧ t < I.d j

instance (t : ℕ) (j : Fin I.jobs) : Decidable (Active t j) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (I)

/-- The time horizon: every job has finished by then. -/
def horizon : ℕ := Finset.univ.sup I.d

/-- The total weight of the jobs a state shows as *beginning* at time `t`. -/
def freshWeight (t : ℕ) (s : State I) : ℕ :=
  ∑ j, if (∃ i, s i = some j) ∧ I.start j = t then I.w j else 0

/-- A state that could be the machine occupancy at time `t`: every occupant is eligible
and active, and no job occupies two machines. -/
def ValidState (t : ℕ) (s : State I) : Prop :=
  (∀ i j, s i = some j → i ∈ I.eligible j ∧ Active t j) ∧
  (∀ i i' j, s i = some j → s i' = some j → i = i')

instance (t : ℕ) (s : State I) : Decidable (ValidState I t s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The transition relation: state `s` at time `t` may be followed by state `s'` at time
`t + 1`. A job still running continues on its machine, and a job appearing at `t + 1`
that had already started must have been there at `t`. -/
def Step (t : ℕ) (s s' : State I) : Prop :=
  ValidState I (t + 1) s' ∧
  (∀ i j, s i = some j → t + 1 < I.d j → s' i = some j) ∧
  (∀ i j, s' i = some j → I.start j ≤ t → s i = some j)

instance (t : ℕ) (s s' : State I) : Decidable (Step I t s s') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {I}

variable (I)

/-- **The dynamic program.** A recursion on the time index: the value of a state at
`t + 1` is the best value of a predecessor, plus the weight of the jobs beginning then. -/
def dp : ℕ → State I → WithBot ℕ
  | 0, s => if ValidState I 0 s then (freshWeight I 0 s : WithBot ℕ) else ⊥
  | t + 1, s' =>
      ((Finset.univ.filter fun s => Step I t s s').sup fun s => dp t s)
        + (freshWeight I (t + 1) s' : WithBot ℕ)

/-- The value the algorithm returns: the table at the horizon, with every machine idle. -/
def solve : WithBot ℕ := dp I (horizon I) fun _ => none

end Lax888481.DynamicProgram
end
