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
end Lax496464.Conditions
end

-- Lax496464.EstOrder
section
namespace Lax496464.EstOrder.DistinctEndpoints
end Lax496464.EstOrder.DistinctEndpoints

namespace Lax496464.EstOrder

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The jobs are numbered in nondecreasing order of their start times. -/
def EstOrdered (I : Instance) : Prop := ∀ i j : I.Job, i ≤ j → s i ≤ s j

end Lax496464.EstOrder
end

-- Lax496464.ProperInstances
section
namespace Lax496464.ProperInstances
end Lax496464.ProperInstances
end

-- Lax496464.Greedy
section
namespace Lax496464.Greedy

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- **One greedy step**, with common preprocessing time `p`: from `A` to `next` on
reaching job `j`. Either `j` is added, or a job of largest due date is dropped from
`A ∪ {j}`. -/
def Step (p : ℕ) (A next : Finset I.Job) (j : I.Job) : Prop :=
  (((A.card : ℤ) + 1) * p ≤ s j ∧ (running I A (s j)).card < I.machines ∧
      next = insert j A) ∨
  ((s j < ((A.card : ℤ) + 1) * p ∨ I.machines ≤ (running I A (s j)).card) ∧
    ∃ c ∈ insert j A, (∀ i ∈ insert j A, (I.d i : ℤ) ≤ (I.d c : ℤ)) ∧
      next = (insert j A).erase c)

end Lax496464.Greedy
end

-- Lax496464.Lemma4
section
namespace Lax496464.Lemma4

open Lax496464.FlowShop Lax496464.FlowShop.Instance

open Lax496464.EstOrder Lax496464.Greedy

variable (I : Instance)

/-- **The greedy is optimal.** Its final set is a feasible set of largest cardinality. -/
axiom greedy_card_max (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p)
    (hq : ∀ i : I.Job, 0 < I.q i)
    (S : ℕ → Finset I.Job) (h0 : S 0 = ∅)
    (hrun : ∀ k, ∀ hk : k < I.jobs, Step I p (S k) (S (k + 1)) ⟨k, hk⟩) :
    Feasible I (S I.jobs) ∧
      ∀ B : Finset I.Job, Feasible I B → B.card ≤ (S I.jobs).card

end Lax496464.Lemma4
end
