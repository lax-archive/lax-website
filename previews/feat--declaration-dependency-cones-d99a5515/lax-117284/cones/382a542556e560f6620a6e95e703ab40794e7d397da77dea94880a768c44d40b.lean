-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
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

/-- The processing time of client `j`'s job on day `i`, read off unnumbered indices and
`1` outside the instance, so that a construction reading another instance need not carry
the proofs that its indices are in range. -/
def pAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.p ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

/-- The due date of client `j`'s job on day `i`, and `1` outside the instance. -/
def dAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.d ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

theorem pAt_pos (i j : ℕ) : 0 < I.pAt i j := by
  unfold pAt
  split
  · split
    · exact I.p_pos _ _
    · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one

theorem pAt_le_dAt (i j : ℕ) : I.pAt i j ≤ I.dAt i j := by
  unfold pAt dAt
  split
  · split
    · exact I.p_le_d _ _
    · exact Nat.le_refl 1
  · exact Nat.le_refl 1

end Instance

end Lax117284.Scheduling
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems
end Lax117284.Problems
end

-- Lax117284.Corollary8
section
namespace Lax117284.Corollary8

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- A time later than every due date of `I`. -/
def bound (I : Instance) : ℕ :=
  (Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j) + 1

/-- **The instance with one blocking client and one blocking day added**: the new client's
job ends later than every due date of `I` and starts at time `0`, so on an old day it
conflicts with every job, and on the new day every job ends at that same time, so all jobs
of the new day pairwise conflict. -/
def addBlockingDay (I : Instance) : Instance where
  clients := I.clients + 1
  days := I.days + 1
  p i j :=
    if (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.pAt i j else I.pAt 0 j)
    else bound I
  d i j := if (j : ℕ) < I.clients ∧ (i : ℕ) < I.days then I.dAt i j else bound I
  p_pos i j := by
    have h0 := I.pAt_pos (i : ℕ) (j : ℕ)
    have h1 := I.pAt_pos 0 (j : ℕ)
    have h2 : 0 < bound I := by simp [bound]
    split_ifs <;> omega
  p_le_d i j := by
    have h1 := I.pAt_le_dAt (i : ℕ) (j : ℕ)
    have h2 : I.dAt (i : ℕ) (j : ℕ) ≤ bound I := by
      unfold Instance.dAt bound
      split_ifs with h h'
      · have h3 : I.d ⟨(i : ℕ), h⟩ ⟨(j : ℕ), h'⟩ ≤
            Finset.univ.sup fun j' => I.d ⟨(i : ℕ), h⟩ j' :=
          Finset.le_sup (Finset.mem_univ _)
        have h4 : (Finset.univ.sup fun j' => I.d ⟨(i : ℕ), h⟩ j') ≤
            Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
          Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ _)
        omega
      · omega
      · omega
    have h5 : I.pAt 0 (j : ℕ) ≤ I.dAt 0 (j : ℕ) := I.pAt_le_dAt 0 (j : ℕ)
    have h6 : I.dAt 0 (j : ℕ) ≤ bound I := by
      unfold Instance.dAt bound
      split_ifs with h h'
      · have h3 : I.d ⟨0, h⟩ ⟨(j : ℕ), h'⟩ ≤ Finset.univ.sup fun j' => I.d ⟨0, h⟩ j' :=
          Finset.le_sup (Finset.mem_univ _)
        have h4 : (Finset.univ.sup fun j' => I.d ⟨0, h⟩ j') ≤
            Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
          Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ _)
        omega
      · omega
      · omega
    split_ifs <;> omega

/-- **Adding a blocking client and a blocking day preserves one-fairness.** -/
axiom addBlockingDay_correct (I : Instance) (hm : 0 < I.days) :
    I.HasKFairSchedule 1 ↔ (addBlockingDay I).HasKFairSchedule 1

end Lax117284.Corollary8
end
