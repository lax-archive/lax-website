-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284.Scheduling

/-- An instance of fair repetitive interval scheduling: `clients` clients each submitting
one job on each of `days` days, where client `j`'s job on day `i` has processing time
`p i j` and due date `d i j`. A job takes some time and does not start before time `0`. -/
structure Instance where
  /-- The number `n` of clients. -/
  clients : ℕ
  /-- The number `m` of days. -/
  days : ℕ
  /-- The processing time `p i j` of client `j`'s job on day `i`. -/
  p : Fin days → Fin clients → ℕ
  /-- The due date `d i j` of client `j`'s job on day `i`. -/
  d : Fin days → Fin clients → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d i j

namespace Instance

variable (I : Instance)

/-- The interval `(d i j - p i j, d i j]` occupied by client `j`'s job on day `i`: the job
is completed exactly at its due date. -/
def job (i : Fin I.days) (j : Fin I.clients) : Set ℕ :=
  Set.Ioc (I.d i j - I.p i j) (I.d i j)

/-- Clients `j` and `j'` **conflict on day `i`**: their day-`i` jobs share a time point, so
the machine of that day can execute at most one of them. -/
def Conflict (i : Fin I.days) (j j' : Fin I.clients) : Prop :=
  (I.job i j ∩ I.job i j').Nonempty

/-- A **schedule** names, for each day, the clients whose job is executed that day. -/
abbrev Schedule := Fin I.days → Finset (Fin I.clients)

variable {I}

/-- A schedule is **feasible** if the jobs it executes on any one day are pairwise
non-conflicting. -/
def Feasible (σ : I.Schedule) : Prop :=
  ∀ i, (σ i : Set (Fin I.clients)).Pairwise fun j j' => ¬ I.Conflict i j j'

/-- `∑_i Z_{i,j}`, the number of days on which client `j`'s job is executed. -/
def served (σ : I.Schedule) (j : Fin I.clients) : ℕ :=
  (Finset.univ.filter fun i => j ∈ σ i).card

/-- A schedule is **fair** for the parameters `k` if every client `j` is served on at least
`k j` days. -/
def Fair (k : Fin I.clients → ℕ) (σ : I.Schedule) : Prop := ∀ j, k j ≤ served σ j

variable (I)

/-- **The question of `1 | k_j, rep | min_j ∑_i Z_{i,j}`**: is there a feasible schedule
serving every client `j` on at least `k j` days? -/
def HasFairSchedule (k : Fin I.clients → ℕ) : Prop :=
  ∃ σ : I.Schedule, Feasible σ ∧ Fair k σ

/-- **The question of `1 | rep | min_j ∑_i Z_{i,j}`**: the uniform case, in which every
client carries the same fairness parameter `k`. -/
def HasKFairSchedule (k : ℕ) : Prop := I.HasFairSchedule fun _ => k

end Instance

end Lax117284.Scheduling
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.JustInTime
section
namespace Lax117284.JustInTime

open Lax434930.PolynomialTime

/-- An instance of `R || ∑_j Z_j`: `jobs` jobs and `machines` unrelated machines, where job
`j` has due date `d j` and processing time `p i j` on machine `i`. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p i j` of job `j` on machine `i`. -/
  p : Fin machines → Fin jobs → ℕ
  /-- The due date `d j` of job `j`, the same on every machine. -/
  d : Fin jobs → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d j

namespace Instance

variable (R : Instance)

/-- The interval `(d j - p i j, d j]` occupied by job `j` when it is executed just in time
on machine `i`. -/
def job (i : Fin R.machines) (j : Fin R.jobs) : Set ℕ :=
  Set.Ioc (R.d j - R.p i j) (R.d j)

/-- Jobs `j` and `j'` **overlap on machine `i`**: executing both just in time on that
machine would have them share a time point. -/
def Overlap (i : Fin R.machines) (j j' : Fin R.jobs) : Prop :=
  (R.job i j ∩ R.job i j').Nonempty

/-- **The question of `R || ∑_j Z_j` at its maximum value**: can every job be executed just
in time, that is, is there an assignment of the jobs to machines under which no two jobs of
a machine overlap? -/
def AllJustInTime : Prop :=
  ∃ f : Fin R.jobs → Fin R.machines,
    ∀ j j', j ≠ j' → f j = f j' → ¬ R.Overlap (f j) j j'

end Instance

end Lax117284.JustInTime
end

-- Lax117284.Theorem11
section
namespace Lax117284.Theorem11

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- **The instance of Theorem 11**: clients are jobs, days are machines, the due date of a
client is that of its job and so does not depend on the day. -/
def inst (R : JustInTime.Instance) : Instance where
  clients := R.jobs
  days := R.machines
  p i j := R.p i j
  d _ j := R.d j
  p_pos := R.p_pos
  p_le_d := R.p_le_d

/-- **The construction is correct**: every job can be executed just in time exactly when
every client can be served on at least one day. -/
axiom correct (R : JustInTime.Instance) :
    R.AllJustInTime ↔ (inst R).HasKFairSchedule 1

end Lax117284.Theorem11
end
