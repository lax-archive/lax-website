-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Card
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

/-- `p_{i,j} = 1`: the processing times are **unit**. -/
def UnitP : Prop := ∀ i j, I.p i j = 1

end Instance

end Lax117284.Scheduling
end

-- Lax117284.Theorem10
section
namespace Lax117284.Theorem10

open Lax117284.Scheduling

variable (I : Instance)

/-- The far side of the bipartite graph: a slot vertex `u_{i,t}` for a day and a time, and
a rejection vertex `w_{l,j}` for a client. -/
def Target : Type := (Fin I.days × ℕ) ⊕ (ℕ × Fin I.clients)

/-- The edges of the bipartite graph: the job vertex `v_{i,j}` is joined to the slot vertex
of its own day and due date, and to the `m - k` rejection vertices of its own client. -/
def Matchable (k : ℕ) (v : Fin I.days × Fin I.clients) (t : Target I) : Prop :=
  t = Sum.inl (v.1, I.d v.1 v.2) ∨ ∃ l < I.days - k, t = Sum.inr (l, v.2)

/-- The bipartite graph has a matching saturating every job vertex. -/
def HasFullMatching (k : ℕ) : Prop :=
  ∃ f : Fin I.days × Fin I.clients → Target I,
    Function.Injective f ∧ ∀ v, Matchable I k v (f v)

/-- **Theorem 10.** With unit processing times and `k ≤ m`, a `k`-fair schedule exists
exactly when the bipartite graph has a matching saturating every job vertex. -/
axiom hasKFairSchedule_iff_hasFullMatching {I : Instance} (h : I.UnitP) {k : ℕ}
    (hk : k ≤ I.days) : I.HasKFairSchedule k ↔ HasFullMatching I k

end Lax117284.Theorem10
end
