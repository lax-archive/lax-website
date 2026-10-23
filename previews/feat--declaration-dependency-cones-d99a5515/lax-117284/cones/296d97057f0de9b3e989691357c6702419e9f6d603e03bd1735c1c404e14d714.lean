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

variable {I}

variable (I)

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
end Lax117284.ConflictGraph
end

-- Lax117284.InstanceEncoding
section
namespace Lax117284.InstanceEncoding

open Lax117284.Scheduling

/-- The number of clients declared by a word: its first entry. -/
def clientCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of days declared by a word: its second entry. -/
def dayCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The processing time of client `j`'s job on day `i`: the processing times follow the two
header entries, day by day. -/
def proc (x : List ℕ) (i j : ℕ) : ℕ := x.getD (2 + i * clientCount x + j) 0

/-- The due date of client `j`'s job on day `i`: the due dates follow the processing
times. -/
def due (x : List ℕ) (i j : ℕ) : ℕ :=
  x.getD (2 + dayCount x * clientCount x + i * clientCount x + j) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s clients. -/
  clientCount_eq : clientCount x = I.clients
  /-- The word declares `I`'s days. -/
  dayCount_eq : dayCount x = I.days
  /-- The word consists of the two header entries and the two arrays of one number per
  job. -/
  length_eq : x.length = 2 + 2 * I.days * I.clients
  /-- The processing times are `I`'s. -/
  proc_eq : ∀ (i : Fin I.days) (j : Fin I.clients), proc x i j = I.p i j
  /-- The due dates are `I`'s. -/
  due_eq : ∀ (i : Fin I.days) (j : Fin I.clients), due x i j = I.d i j

/-- The instance with no client and no day, the value of the decoding on a word that
encodes no instance. -/
def empty : Instance where
  clients := 0
  days := 0
  p := fun i => i.elim0
  d := fun i => i.elim0
  p_pos := fun i => i.elim0
  p_le_d := fun i => i.elim0

open Classical in
/-- The instance a word encodes, and `empty` on a word that encodes none. -/
noncomputable def decode (x : List ℕ) : Instance :=
  if h : ∃ I, EncodesInstance x I then h.choose else empty

end Lax117284.InstanceEncoding
end
