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
