-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
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

variable {I}

variable (I)

end Instance

end Lax888481.Scheduling
end

-- Lax888481.InstanceEncoding
section
namespace Lax888481.InstanceEncoding

open Lax888481.Scheduling

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The processing time of job `j`: the processing times follow the two header
entries. -/
def proc (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + j) 0

/-- The deadline of job `j`: the deadlines follow the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + jobCount x + j) 0

/-- The weight of job `j`: the weights follow the deadlines. -/
def wt (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

/-- The `i`-th offset: the `n+1` offsets follow the weights. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + 3 * jobCount x + i) 0

/-- The `t`-th entry of the target array, which follows the offsets. -/
def target (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + 4 * jobCount x + t) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s jobs. -/
  jobCount_eq : jobCount x = I.jobs
  /-- The word declares `I`'s machines. -/
  machineCount_eq : machineCount x = I.machines
  /-- The word consists of the two header entries, the three arrays of one number per
  job, the `n+1` offsets, and a target array as long as the last offset says. -/
  length_eq : x.length = 3 + 4 * I.jobs + offset x I.jobs
  /-- The processing times are `I`'s. -/
  proc_eq : ∀ j : Fin I.jobs, proc x j = I.p j
  /-- The deadlines are `I`'s. -/
  due_eq : ∀ j : Fin I.jobs, due x j = I.d j
  /-- The weights are `I`'s. -/
  wt_eq : ∀ j : Fin I.jobs, wt x j = I.w j
  /-- The block of the first job begins at the start of the target array. -/
  offset_zero : offset x 0 = 0
  /-- The offsets are nondecreasing, so they cut the target array into one block per
  job. -/
  offset_mono : ∀ j < I.jobs, offset x j ≤ offset x (j + 1)
  /-- Every entry of the target array is a machine. -/
  target_lt : ∀ t < offset x I.jobs, target x t < I.machines
  /-- The block of a job lists exactly its eligible machines. -/
  eligible_iff : ∀ (j : Fin I.jobs) (i : Fin I.machines),
    i ∈ I.eligible j ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ target x t = i

/-- The word `x` presents the instance `I` together with the threshold `W`: an instance
block followed by the single entry `W`. -/
def EncodesDecisionInstance (x : List ℕ) (I : Instance) (W : ℕ) : Prop :=
  ∃ y, x = y ++ [W] ∧ EncodesInstance y I

end Lax888481.InstanceEncoding
end
