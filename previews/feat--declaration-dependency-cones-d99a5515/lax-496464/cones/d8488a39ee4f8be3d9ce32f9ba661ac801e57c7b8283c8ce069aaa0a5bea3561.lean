-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

-- Lax496464.FlowShop
section
namespace Lax496464.FlowShop

/-- An instance of the two-stage flexible flow shop: `jobs` jobs, `machines` identical
second-stage machines, and for each job a preprocessing time, a processing time, a due
date and a weight. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of identical second-stage machines. -/
  machines : ℕ
  /-- The first-stage (preprocessing) time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The second-stage (processing) time `q j` of job `j`. -/
  q : Fin jobs → ℕ
  /-- The due date `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

/-- A job of the instance. -/
abbrev Job : Type := Fin I.jobs

variable {I}

/-- `s j = d j - q j`: the time at which job `j`'s second operation must start if `j` is
to be completed just in time, and hence a deadline for its first operation. -/
def s (j : I.Job) : ℤ := (I.d j : ℤ) - I.q j

/-- Jobs `i` and `j` **conflict** when the intervals `[s i, d i)` and `[s j, d j)` of
their second operations overlap. Conflicting jobs cannot share a second-stage machine. -/
def Conflict (i j : I.Job) : Prop := s i < (I.d j : ℤ) ∧ s j < (I.d i : ℤ)

/-- A **just-in-time schedule of `Z`**: a schedule of the jobs in `Z` completing every
one of them exactly at its due date. `pre j` is the start time of `j`'s first operation
and `mach j` the second-stage machine running its second operation; the second operation
needs no start time, because just-in-time completion pins it to `[s j, d j)`. -/
structure JITSchedule (Z : Finset I.Job) where
  /-- The start time of the first operation of job `j`. -/
  pre : I.Job → ℤ
  /-- The second-stage machine of job `j`. -/
  mach : I.Job → ℕ
  /-- No operation starts before time `0`. -/
  pre_nonneg : ∀ j ∈ Z, 0 ≤ pre j
  /-- The preprocessing of `j` is finished by the time its second operation must start. -/
  pre_le_s : ∀ j ∈ Z, pre j + I.p j ≤ s j
  /-- The first stage is a single machine: its operations do not overlap. -/
  pre_disjoint : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
    pre i + I.p i ≤ pre j ∨ pre j + I.p j ≤ pre i
  /-- Only the `m` machines of the instance are used. -/
  mach_lt : ∀ j ∈ Z, mach j < I.machines
  /-- Conflicting jobs do not share a second-stage machine. -/
  mach_indep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → mach i = mach j → ¬ Conflict i j

variable (I)

/-- `Z` is **feasible**: its jobs can all be completed just in time. -/
def Feasible (Z : Finset I.Job) : Prop := Nonempty (JITSchedule Z)

/-- The jobs of `Z` whose second operation is running at time `t`. -/
def running (Z : Finset I.Job) (t : ℤ) : Finset I.Job :=
  Z.filter fun i => s i ≤ t ∧ t < (I.d i : ℤ)

end Instance

end Lax496464.FlowShop
end

-- Lax496464.Conditions
section
namespace Lax496464.Conditions

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- **Condition 1.** `Z` can be preprocessed in time: for every `j ∈ Z`, the jobs of `Z`
starting no later than `j` fit together into `[0, s j)`. -/
def Preprocessable (Z : Finset I.Job) : Prop :=
  ∀ j ∈ Z, ∑ i ∈ Z.filter (fun i => s i ≤ s j), (I.p i : ℤ) ≤ s j

end Lax496464.Conditions
end

-- Lax496464.Feasibility
section
namespace Lax496464.Feasibility

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Conditions

/-- **Observation 2.** Feasibility is decided by Condition 1 together with a count, at
the start time of each selected job, of the selected jobs running then. -/
axiom feasible_iff_conditions (I : Instance) {Z : Finset I.Job}
    (hq : ∀ j ∈ Z, 0 < I.q j) :
    Feasible I Z ↔
      Preprocessable I Z ∧ ∀ j ∈ Z, (running I Z (s j)).card ≤ I.machines

end Lax496464.Feasibility
end
