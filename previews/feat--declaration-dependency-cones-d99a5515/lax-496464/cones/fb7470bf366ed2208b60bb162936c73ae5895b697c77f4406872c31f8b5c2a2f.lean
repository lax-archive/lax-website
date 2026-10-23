-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

-- Lax496464.FlowShop
section
namespace Lax496464.FlowShop.Instance.JITSchedule
end Lax496464.FlowShop.Instance.JITSchedule

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

variable (I)

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

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The jobs are numbered in nondecreasing order of their start times. -/
def EstOrdered (I : Instance) : Prop := ∀ i j : I.Job, i ≤ j → s i ≤ s j

/-- No two of the `2n` endpoints `s j` and `d j` coincide. -/
structure DistinctEndpoints (I : Instance) : Prop where
  /-- Distinct jobs have distinct start times. -/
  start_inj : ∀ i j : I.Job, s i = s j → i = j
  /-- Distinct jobs have distinct due dates. -/
  due_inj : ∀ i j : I.Job, (I.d i : ℤ) = (I.d j : ℤ) → i = j
  /-- No start time is a due date. -/
  start_ne_due : ∀ i j : I.Job, s i ≠ (I.d j : ℤ)

/-- The rescaled instance `d' j = (n+1) d j + j`, `q' j = (n+1) q j`, `p' j = (n+1) p j`,
with the weights unchanged. -/
def scale (I : Instance) : Instance where
  jobs := I.jobs
  machines := I.machines
  p j := (I.jobs + 1) * I.p j
  q j := (I.jobs + 1) * I.q j
  d j := (I.jobs + 1) * I.d j + (j : ℕ)
  w j := I.w j

end Lax496464.EstOrder
end

-- Lax496464.Normalization
section
namespace Lax496464.Normalization

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder

/-- The rescaling separates the endpoints, and keeps the jobs in earliest-start-time
order. -/
axiom scale_distinctEndpoints (I : Instance) (h : EstOrdered I) (hq : ∀ i : I.Job, 0 < I.q i) :
    DistinctEndpoints (scale I) ∧ EstOrdered (scale I)

end Lax496464.Normalization
end
