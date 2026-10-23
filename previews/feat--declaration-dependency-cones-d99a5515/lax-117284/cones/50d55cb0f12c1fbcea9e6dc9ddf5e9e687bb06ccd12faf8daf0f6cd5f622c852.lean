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

end Lax117284.Theorem10
end
