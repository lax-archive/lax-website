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

variable {I}

variable (I)

end Instance

end Lax117284.Scheduling
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

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

open Lax117284.Scheduling Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the number of clients, the number of days, then the
processing time and the due date of every job. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.clients ++ encodeNat I.days ++
    (List.finRange I.days).flatMap fun i =>
      (List.finRange I.clients).flatMap fun j => encodeNat (I.p i j) ++ encodeNat (I.d i j)

/-- An instance of `1 | rep | min_j ∑_i Z_{i,j}`: an instance followed by the fairness
parameter. -/
def encodeUniform (I : Instance) (k : ℕ) : Word := encodeInstance I ++ encodeNat k

/-- An instance with one client and no day, whose only client cannot be served at all. -/
def blocked : Instance where
  clients := 1
  days := 0
  p := fun i => i.elim0
  d := fun i => i.elim0
  p_pos := fun i => i.elim0
  p_le_d := fun i => i.elim0

/-- A word belonging to no language of this submission: the instance `blocked` with the
fairness parameter `1`. It is the image a reduction gives the words it must reject. -/
def rejected : Word := encodeUniform blocked 1

end Lax117284.Problems
end

-- Lax117284.JustInTime
section
namespace Lax117284.JustInTime

open Lax434930.PolynomialTime

/-- An instance of `R || ∑_j Z_j`: `jobs` jobs and `machines` unrelated machines, where job
`j` has due date `d j` and processing time `p i j` on machine `i`. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p i j` of job `j` on machine `i`. -/
  p : Fin machines → Fin jobs → ℕ
  /-- The due date `d j` of job `j`, the same on every machine. -/
  d : Fin jobs → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d j

namespace Instance

variable (R : Instance)

end Instance

/-- An instance as a binary word: the number of jobs, the number of machines, the due
dates, and then the processing times machine by machine. -/
def encodeInstance (R : Instance) : Word :=
  Problems.encodeNat R.jobs ++ Problems.encodeNat R.machines ++
    ((List.finRange R.jobs).flatMap fun j => Problems.encodeNat (R.d j)) ++
    (List.finRange R.machines).flatMap fun i =>
      (List.finRange R.jobs).flatMap fun j => Problems.encodeNat (R.p i j)

end Lax117284.JustInTime
end

-- Lax117284.Theorem11
section
namespace Lax117284.Theorem11

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- **The instance of Theorem 11**: clients are jobs, days are machines, the due date of a
client is that of its job and so does not depend on the day. -/
def inst (R : JustInTime.Instance) : Instance where
  clients := R.jobs
  days := R.machines
  p i j := R.p i j
  d _ j := R.d j
  p_pos := R.p_pos
  p_le_d := R.p_le_d

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance of
`R || ∑_j Z_j` is sent to the encoding of the constructed instance with the fairness
parameter `1`, and every other word to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ R : JustInTime.Instance, JustInTime.encodeInstance R = w then
    encodeUniform (inst h.choose) 1
  else rejected

end Lax117284.Theorem11
end
