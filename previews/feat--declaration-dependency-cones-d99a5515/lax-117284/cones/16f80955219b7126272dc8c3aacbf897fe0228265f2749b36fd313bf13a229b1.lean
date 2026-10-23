-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
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

/-- `p_{i,j} = p_j`: the processing times are **day-independent**. -/
def DayIndepP : Prop := ∀ i i' j, I.p i j = I.p i' j

/-- `d_{i,j} = d_j`: the due dates are **day-independent**. -/
def DayIndepD : Prop := ∀ i i' j, I.d i j = I.d i' j

end Instance

end Lax117284.Scheduling
end

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax117284.ConflictGraph
section
namespace Lax117284.ConflictGraph

open Lax117284.Scheduling

/-- Conflict is a symmetric relation: the two jobs share a time point either way. -/
theorem conflict_symm {I : Instance} {i : Fin I.days} {j j' : Fin I.clients}
    (h : I.Conflict i j j') : I.Conflict i j' j :=
  let ⟨t, ht⟩ := h; ⟨t, ht.2, ht.1⟩

variable (I : Instance)

/-- **The day `i` conflict graph** of `I`: two distinct clients are adjacent when their
jobs of day `i` conflict. -/
def dayGraph (i : Fin I.days) : SimpleGraph (Fin I.clients) where
  Adj j j' := j ≠ j' ∧ I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, conflict_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Lax117284.ConflictGraph
end

-- Lax117284.Theorem13
section
namespace Lax117284.Theorem13

open Lax117284.Scheduling Lax117284.ConflictGraph

variable {I : Instance}

/-- **Theorem 13.** With day-independent due dates and processing times, a `k`-fair
schedule exists exactly when `k` times the chromatic number of the conflict graph is at
most the number of days. -/
axiom hasKFairSchedule_iff_mul_chromaticNumber_le (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i₀ : Fin I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ (k : ℕ∞) * (dayGraph I i₀).chromaticNumber ≤ I.days

end Lax117284.Theorem13
end
