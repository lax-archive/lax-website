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

variable {I}

variable (I)

/-- The processing time of client `j`'s job on day `i`, read off unnumbered indices and
`1` outside the instance, so that a construction reading another instance need not carry
the proofs that its indices are in range. -/
def pAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.p ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

/-- The due date of client `j`'s job on day `i`, and `1` outside the instance. -/
def dAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.d ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

@[simp] theorem pAt_coe (i : Fin I.days) (j : Fin I.clients) : I.pAt i j = I.p i j := by
  simp [pAt, i.isLt, j.isLt]

@[simp] theorem dAt_coe (i : Fin I.days) (j : Fin I.clients) : I.dAt i j = I.d i j := by
  simp [dAt, i.isLt, j.isLt]

/-- Whether clients `j` and `j'` conflict on day `i`, read off unnumbered indices and in
the arithmetic form: each of the two jobs starts before the other one is due. It is this
form of the condition that a construction can decide. -/
def ConflictAt (i j j' : ℕ) : Prop :=
  I.dAt i j - I.pAt i j < I.dAt i j' ∧ I.dAt i j' - I.pAt i j' < I.dAt i j

/-- **The arithmetic and the geometric form of conflict agree.** -/
theorem conflictAt_iff (i : Fin I.days) (j j' : Fin I.clients) :
    I.ConflictAt i j j' ↔ I.Conflict i j j' := by
  have h1 := I.p_pos i j
  have h2 := I.p_le_d i j
  have h3 := I.p_pos i j'
  have h4 := I.p_le_d i j'
  simp only [ConflictAt, Conflict, job, pAt_coe, dAt_coe, Set.Nonempty, Set.mem_inter_iff,
    Set.mem_Ioc]
  constructor
  · intro h
    exact ⟨min (I.d i j) (I.d i j'), by omega, by omega⟩
  · rintro ⟨t, ⟨h5, h6⟩, h7, h8⟩
    omega

end Instance

end Lax117284.Scheduling
end
