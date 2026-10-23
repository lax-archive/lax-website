-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
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

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

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

/-- An instance of `1 | k_j, rep | min_j ∑_i Z_{i,j}`: an instance followed by one
fairness parameter per client. -/
def encodePerClient (I : Instance) (k : Fin I.clients → ℕ) : Word :=
  encodeInstance I ++ (List.finRange I.clients).flatMap fun j => encodeNat (k j)

/-- **`1 | rep | min_j ∑_i Z_{i,j}` on the class `C`**, as a language: the words encoding
an instance of `C` with a fairness parameter for which a fair schedule exists. -/
def Uniform (C : Instance → ℕ → Prop) : Language :=
  {w | ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ C I k ∧ I.HasKFairSchedule k}

/-- **`1 | k_j, rep | min_j ∑_i Z_{i,j}` on the class `C`**, as a language. -/
def PerClient (C : (I : Instance) → (Fin I.clients → ℕ) → Prop) : Language :=
  {w | ∃ (I : Instance) (k : Fin I.clients → ℕ),
    encodePerClient I k = w ∧ C I k ∧ I.HasFairSchedule k}

/-- The class of all instances and parameters. -/
def any : Instance → ℕ → Prop := fun _ _ => True

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

-- Lax117284.Corollary8
section
namespace Lax117284.Corollary8

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- **The instance without clients and with `m` days.** -/
def noClients (m : ℕ) : Instance where
  clients := 0
  days := m
  p _ j := j.elim0
  d _ j := j.elim0
  p_pos _ j := j.elim0
  p_le_d _ j := j.elim0

end Lax117284.Corollary8
end

-- Lax117284.Lemma15
section
namespace Lax117284.Lemma15

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- A time not before any due date of `I`. -/
def dmax (I : Instance) : ℕ := Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j

/-- The length of the job the two new clients share: longer than the stretch of private
jobs, so that it contains all of them. -/
def span (I : Instance) : ℕ := I.clients + 1

/-- **The instance of Lemma 15**: `2m` days, the `n` clients of `I` together with two new
ones, and the uniform fairness parameter `m`. -/
def inst (I : Instance) (k : Fin I.clients → ℕ) : Instance where
  clients := I.clients + 2
  days := 2 * I.days
  p i j :=
    if (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.pAt i j else 1)
    else span I
  d i j :=
    if hj : (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.dAt i j
        else if (i : ℕ) - I.days < k ⟨j, hj⟩ then dmax I + ((j : ℕ) + 1)
          else dmax I + span I + ((j : ℕ) + 1))
    else dmax I + span I
  p_pos i j := by
    have h0 := I.pAt_pos (i : ℕ) (j : ℕ)
    have hs : span I = I.clients + 1 := rfl
    split_ifs <;> omega
  p_le_d i j := by
    have h1 := I.pAt_le_dAt (i : ℕ) (j : ℕ)
    have hs : span I = I.clients + 1 := rfl
    split_ifs <;> omega

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance with per-client
parameters not exceeding its number of days is sent to the encoding of the constructed
instance with the parameter `m`, an instance without clients to a fixed yes-instance, and
every other word to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : Fin I.clients → ℕ),
      encodePerClient I k = w ∧ ∀ j, k j ≤ I.days then
    if h.choose.clients = 0 then encodeUniform (Corollary8.noClients 0) 0
    else encodeUniform (inst h.choose h.choose_spec.choose) h.choose.days
  else rejected

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ PerClient (fun I k => ∀ j, k j ≤ I.days) ↔ reduce w ∈ Uniform any

end Lax117284.Lemma15
end
