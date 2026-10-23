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

/-- A schedule assigns each job an eligible machine, or nothing. -/
abbrev Schedule := Fin I.jobs → Option (Fin I.machines)

variable {I}

variable (I)

end Instance

end Lax888481.Scheduling
end

-- Lax888481.DynamicProgram
section
namespace Lax888481.DynamicProgram.dp
end Lax888481.DynamicProgram.dp

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

variable {I}

/-- The machine occupancy at time `t` of the schedule `σ`. -/
noncomputable def runOf (σ : I.Schedule) (t : ℕ) : State I := fun i =>
  if h : ∃ j, σ j = some i ∧ Active t j then some h.choose else none

variable (I)

end Lax888481.DynamicProgram
end
