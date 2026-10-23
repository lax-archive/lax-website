-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Finset.Lattice.Fold

-- Lax470956.Scheduling
section
namespace Lax470956.Scheduling

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

/-- Jobs `j` and `j'` *overlap*: their half-open intervals meet. -/
def Overlap (j j' : Fin I.jobs) : Prop :=
  I.start j < I.d j' ∧ I.start j' < I.d j

/-- A schedule assigns each job an eligible machine, or nothing. -/
abbrev Schedule := Fin I.jobs → Option (Fin I.machines)

variable {I}

/-- A schedule is *feasible* if it places every scheduled job on an eligible machine and
never places two overlapping jobs on the same machine. -/
def Feasible (σ : I.Schedule) : Prop :=
  (∀ j i, σ j = some i → i ∈ I.eligible j) ∧
  (∀ j j' i, j ≠ j' → I.Overlap j j' → σ j = some i → σ j' ≠ some i)

/-- The weight of a schedule: the total weight of the jobs it schedules. -/
def weight (σ : I.Schedule) : ℕ := ∑ j, (σ j).elim 0 fun _ => I.w j

variable (I)

end Instance

end Lax470956.Scheduling
end

-- Lax470956.DynamicProgram
section
namespace Lax470956.DynamicProgram.dp
end Lax470956.DynamicProgram.dp

namespace Lax470956.DynamicProgram

open Lax470956.Scheduling Lax470956.Scheduling.Instance

variable (I : Instance)

variable {I}

instance (j j' : Fin I.jobs) : Decidable (I.Overlap j j') :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (σ : I.Schedule) : Decidable (Feasible σ) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (I)

/-- The value of an optimal schedule. -/
def optimum : ℕ := (Finset.univ.filter fun σ : I.Schedule => Feasible σ).sup weight

variable {I}

variable (I)

end Lax470956.DynamicProgram
end

-- Lax470956.Preprocessing
section
namespace Lax470956.Preprocessing

open Lax470956.Scheduling Lax470956.Scheduling.Instance Lax470956.DynamicProgram

variable (I : Instance)

/-- `j` is strictly better than `j'`: heavier, or equally heavy and earlier in index
order. -/
def Better (j j' : Fin I.jobs) : Prop :=
  I.w j' < I.w j ∨ (I.w j' = I.w j ∧ (j : ℕ) < (j' : ℕ))

instance (j j' : Fin I.jobs) : Decidable (Better I j j') :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The jobs occupying the interval `[dd - pp, dd)` that are eligible on machine `i`. -/
def slotOf (i : Fin I.machines) (dd pp : ℕ) : Finset (Fin I.jobs) :=
  Finset.univ.filter fun j => I.d j = dd ∧ I.p j = pp ∧ i ∈ I.eligible j

/-- The jobs occupying the same interval as `j` that are eligible on machine `i`. -/
def sameSlot (i : Fin I.machines) (j : Fin I.jobs) : Finset (Fin I.jobs) :=
  slotOf I i (I.d j) (I.p j)

/-- How many jobs of `j`'s slot on machine `i` beat `j`. -/
def rank (i : Fin I.machines) (j : Fin I.jobs) : ℕ :=
  ((sameSlot I i j).filter fun j' => Better I j' j).card

/-- **The preprocessing step.** Keep a job when, for some machine it is eligible on, it
is among the `m` best jobs of its interval there. -/
def keep : Finset (Fin I.jobs) :=
  Finset.univ.filter fun j => ∃ i ∈ I.eligible j, rank I i j < I.machines

/-- The best weight achievable by a feasible schedule that uses only jobs from `K`. -/
def optimumOn (K : Finset (Fin I.jobs)) : ℕ :=
  (Finset.univ.filter fun σ : I.Schedule => Feasible σ ∧ ∀ j, σ j ≠ none → j ∈ K).sup
    weight

/-- **Lemma 5.** Preprocessing does not change the optimum: the best weight achievable
using only the kept jobs is the optimum of the whole instance. -/
axiom optimumOn_keep (I : Instance) : optimumOn I (keep I) = optimum I

end Lax470956.Preprocessing
end
