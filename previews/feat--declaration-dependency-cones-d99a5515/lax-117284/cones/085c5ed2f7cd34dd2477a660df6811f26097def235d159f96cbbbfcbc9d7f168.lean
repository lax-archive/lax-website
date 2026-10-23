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

/-- `d_{i,j} = d_j`: the due dates are **day-independent**. -/
def DayIndepD : Prop := ∀ i i' j, I.d i j = I.d i' j

end Instance

end Lax117284.Scheduling
end

-- Lax117284.Theorem12
section
namespace Lax117284.Theorem12

open Lax117284.Scheduling

variable {I : Instance}

/-- The dynamic program of Theorem 12: given the due dates `dd`, the fairness parameter
`k`, the clients still to be served, and for each day the time at which its machine is
free, can every remaining client be served on `k` days? -/
def Program (dd : Fin I.clients → ℕ) (k : ℕ) :
    List (Fin I.clients) → (Fin I.days → ℕ) → Prop
  | [], _ => True
  | j :: rest, free => ∃ S : Finset (Fin I.days), S.card = k ∧
      (∀ i ∈ S, I.p i j + free i ≤ dd j) ∧
      Program dd k rest fun i => if i ∈ S then dd j else free i

/-- **Theorem 12.** With day-independent due dates, an instance admits a `k`-fair schedule
exactly when the dynamic program, applied to the clients in due-date order with every
machine free from time `0`, can serve every client on `k` days. -/
axiom hasKFairSchedule_iff_program (hd : I.DayIndepD) (i₀ : Fin I.days) (k : ℕ)
    {l : List (Fin I.clients)} (hnd : l.Nodup) (hall : ∀ j, j ∈ l)
    (hsorted : l.Pairwise fun a b => I.d i₀ a ≤ I.d i₀ b) :
    I.HasKFairSchedule k ↔ Program (I.d i₀) k l fun _ => 0

end Lax117284.Theorem12
end
