-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

-- Lax496464.ConsecutiveOnes
section
namespace Lax496464
end Lax496464

namespace Lax496464.ConsecutiveOnes
end Lax496464.ConsecutiveOnes
end

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

-- Lax496464.IntegerProgram
section
namespace Lax496464.IntegerProgram

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- The constraint matrix: the rows `inl j` are the prefix sums of constraint (6), the
rows `inr j` the jobs alive at `s j` of constraint (7). -/
def matrix : Matrix (I.Job ⊕ I.Job) I.Job ℤ
  | Sum.inl j, i => if i ≤ j then 1 else 0
  | Sum.inr j, i => if s i ≤ s j ∧ s j < (I.d i : ℤ) then 1 else 0

/-- The right-hand sides: `⌊s j / p⌋` for (6) and `m` for (7). -/
def rhs (p : ℕ) : I.Job ⊕ I.Job → ℤ
  | Sum.inl j => s j / p
  | Sum.inr _ => I.machines

end Lax496464.IntegerProgram
end

-- Lax496464.Lemma5
section
namespace Lax496464.Lemma5

open Lax496464.FlowShop Lax496464.FlowShop.Instance

open Lax496464.EstOrder Lax496464.ProperInstances

open Lax496464.ConsecutiveOnes Lax496464.IntegerProgram

open Matrix

variable (I : Instance)

/-- **The optimum is the optimum.** A `0/1` vector satisfying the constraints with
objective value `W` is exactly a feasible set of weight `W`. -/
axiom ilp_optimum (hest : EstOrdered I) {p : ℕ} (hp : ∀ i : I.Job, I.p i = p) (hp0 : 0 < p)
    (hq : ∀ i : I.Job, 0 < I.q i) (hs : ∀ j : I.Job, 0 ≤ s j) (W : ℕ) :
    (∃ x : I.Job → ℤ, (∀ i, x i = 0 ∨ x i = 1) ∧
        (∀ r, (matrix I *ᵥ x) r ≤ rhs I p r) ∧ ∑ i, (I.w i : ℤ) * x i = W) ↔
      ∃ Z : Finset I.Job, Feasible I Z ∧ weight I Z = W

end Lax496464.Lemma5
end
