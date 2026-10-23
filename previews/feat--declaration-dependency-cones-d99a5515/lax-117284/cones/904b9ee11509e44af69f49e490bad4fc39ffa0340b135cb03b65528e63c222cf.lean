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

end Lax117284.Theorem12
end
