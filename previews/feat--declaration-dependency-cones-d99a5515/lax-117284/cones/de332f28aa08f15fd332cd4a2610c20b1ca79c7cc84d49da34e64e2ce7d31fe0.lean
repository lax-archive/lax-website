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

/-- The processing time of client `j`'s job on day `i`, read off unnumbered indices and
`1` outside the instance, so that a construction reading another instance need not carry
the proofs that its indices are in range. -/
def pAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.p ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

/-- The due date of client `j`'s job on day `i`, and `1` outside the instance. -/
def dAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.d ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

/-- Whether clients `j` and `j'` conflict on day `i`, read off unnumbered indices and in
the arithmetic form: each of the two jobs starts before the other one is due. It is this
form of the condition that a construction can decide. -/
def ConflictAt (i j j' : ℕ) : Prop :=
  I.dAt i j - I.pAt i j < I.dAt i j' ∧ I.dAt i j' - I.pAt i j' < I.dAt i j

instance (i j j' : ℕ) : Decidable (I.ConflictAt i j j') := by
  unfold ConflictAt; infer_instance

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

-- Lax117284.TwoSatisfiability
section
namespace Lax117284.TwoSatisfiability

open Lax434930.PolynomialTime

/-- A **2-CNF formula**: `clauses` clauses over `vars` variables, each clause a pair of
literals, a literal being a variable together with a sign. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses. -/
  clauses : ℕ
  /-- The two literals of each clause. -/
  lit : Fin clauses → Fin 2 → Fin vars × Bool

namespace Formula

variable (φ : Formula)

end Formula

end Lax117284.TwoSatisfiability
end

-- Lax117284.Theorem9
section
namespace Lax117284.Theorem9

open Lax117284.Scheduling Lax117284.Problems Lax117284.TwoSatisfiability

open Lax434930.PolynomialTime Lax429075.Reductions

/-- The variable "client `j`'s job is executed on day `i`", numbered `i·n + j`. The one
further variable, which no meaningful clause names, is the value on indices out of
range. -/
def varIdx (I : Instance) (i j : ℕ) : Fin (I.days * I.clients + 1) :=
  ⟨min (i * I.clients + j) (I.days * I.clients), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The `α`-th literal of clause `c`: the conflict clauses come first, one slot for every
day and ordered pair of clients, then the validation clauses, one slot for every client and
ordered pair of days. An inadmissible slot carries a tautology. -/
def clauseLit (I : Instance) (c : ℕ) (α : Fin 2) : Fin (I.days * I.clients + 1) × Bool :=
  if c < I.days * I.clients * I.clients then
    let i := c / (I.clients * I.clients)
    let r := c % (I.clients * I.clients)
    let j₁ := r / I.clients
    let j₂ := r % I.clients
    if j₁ ≠ j₂ ∧ I.ConflictAt i j₁ j₂ then
      (varIdx I i (if α = 0 then j₁ else j₂), false)
    else (varIdx I i j₁, α = 0)
  else
    let c' := c - I.days * I.clients * I.clients
    let j := c' / (I.days * I.days)
    let r := c' % (I.days * I.days)
    let i₁ := r / I.days
    let i₂ := r % I.days
    if i₁ ≠ i₂ then (varIdx I (if α = 0 then i₁ else i₂) j, true)
    else (varIdx I i₁ j, α = 0)

/-- **The 2-CNF formula of Theorem 9.** -/
def formula (I : Instance) : Formula where
  vars := I.days * I.clients + 1
  clauses := I.days * I.clients * I.clients + I.clients * I.days * I.days
  lit c α := clauseLit I c α

end Lax117284.Theorem9
end
