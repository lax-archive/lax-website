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

/-- The objective value `w(Z) = ∑_{j ∈ Z} w j` of the solution `Z`. -/
def weight (Z : Finset I.Job) : ℕ := ∑ j ∈ Z, I.w j

/-- The jobs of `Z` whose second operation is running at time `t`. -/
def running (Z : Finset I.Job) (t : ℤ) : Finset I.Job :=
  Z.filter fun i => s i ≤ t ∧ t < (I.d i : ℤ)

end Instance

end Lax496464.FlowShop
end

-- Lax496464.Conditions
section
namespace Lax496464.Conditions
end Lax496464.Conditions
end

-- Lax496464.EstOrder
section
namespace Lax496464.EstOrder
end Lax496464.EstOrder

namespace Lax496464.EstOrder.DistinctEndpoints
end Lax496464.EstOrder.DistinctEndpoints
end

-- Lax496464.Sweep
section
namespace Lax496464.Sweep

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- The total preprocessing time of `Z`. -/
def pload (Z : Finset I.Job) : ℤ := ∑ i ∈ Z, (I.p i : ℤ)

/-- The table: a feasible set of weight `W'`, all of whose jobs have started by `t`, is
alive at `t` in exactly `X` and costs at most `P'` to preprocess. -/
def Reachable (t : ℤ) (X : Finset I.Job) (W' : ℕ) (P' : ℤ) : Prop :=
  ∃ Z : Finset I.Job, Feasible I Z ∧ (∀ k ∈ Z, s k ≤ t) ∧
    running I Z t = X ∧ weight I Z = W' ∧ pload I Z ≤ P'

end Lax496464.Sweep
end

-- Lax496464.Lemma2
section
namespace Lax496464.Lemma2

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep

variable (I : Instance)

/-- **Equation (4).** The step across an instant at which job `j` becomes due. -/
axiom reachable_due (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {W' : ℕ} {P' : ℤ}
    (htt : t' < t) (hdj : (I.d j : ℤ) = t)
    (hnos : ∀ k : I.Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, k ≠ j → ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Reachable I t X W' P' ↔
      j ∉ X ∧ (Reachable I t' X W' P' ∨ Reachable I t' (insert j X) W' P')

end Lax496464.Lemma2
end
