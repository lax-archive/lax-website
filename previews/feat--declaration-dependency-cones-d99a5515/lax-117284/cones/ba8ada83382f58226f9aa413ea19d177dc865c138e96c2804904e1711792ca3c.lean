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

-- Lax117284.BoundedSat
section
namespace Lax117284.BoundedSat

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A **[2,3]-bounded 3-SAT formula** over `vars` variables: `twoClauses` clauses of two
literals and `threeClauses` clauses of three literals, in which every literal — a variable
together with a sign — occupies at most two of the positions of the formula. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses of two literals. -/
  twoClauses : ℕ
  /-- The number of clauses of three literals. -/
  threeClauses : ℕ
  /-- The literals of the clauses of two literals. -/
  aLit : Fin twoClauses → Fin 2 → Fin vars × Bool
  /-- The literals of the clauses of three literals. -/
  bLit : Fin threeClauses → Fin 3 → Fin vars × Bool
  /-- Every literal occurs at most twice in the formula. -/
  occ_le_two : ∀ l : Fin vars × Bool,
    (Finset.univ.filter fun o : (Fin twoClauses × Fin 2) ⊕ (Fin threeClauses × Fin 3) =>
      Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o = l).card ≤ 2

namespace Formula

variable (φ : Formula)

end Formula

/-- The literal occupying the occurrence slot `o`, read off unnumbered indices: the two
slots of every clause of two literals come first, then the three slots of every clause of
three literals. Outside the formula the value is the positive literal of the variable `0`.
It is in this form that a construction reads a formula. -/
def litOfSlot (φ : Formula) (o : ℕ) : ℕ × Bool :=
  if o < 2 * φ.twoClauses then
    if hj : o / 2 < φ.twoClauses then
      ((φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).1, (φ.aLit ⟨o / 2, hj⟩ ⟨o % 2, by omega⟩).2)
    else (0, true)
  else
    if hj : (o - 2 * φ.twoClauses) / 3 < φ.threeClauses then
      ((φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).1,
        (φ.bLit ⟨(o - 2 * φ.twoClauses) / 3, hj⟩ ⟨(o - 2 * φ.twoClauses) % 3, by omega⟩).2)
    else (0, true)

/-- Which of the occurrences of its own literal the slot `o` is: the number of earlier
slots carrying the same literal. Under the occurrence bound this is `0` or `1`. -/
def slotRank (φ : Formula) (o : ℕ) : ℕ :=
  (List.range o).countP fun o' => litOfSlot φ o' == litOfSlot φ o

/-- The number of occurrence slots of the formula. -/
def slots (φ : Formula) : ℕ := 2 * φ.twoClauses + 3 * φ.threeClauses

end Lax117284.BoundedSat
end

-- Lax117284.Theorem7
section
namespace Lax117284.Theorem7

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

open Lax429075.Reductions

/-- The number of clients of the construction: three dummies, two per variable, and one per
occurrence slot. -/
def clients (φ : BoundedSat.Formula) : ℕ := 3 + 2 * φ.vars + BoundedSat.slots φ

/-- The due date of client `c` on day `i` of the construction. -/
def due (φ : BoundedSat.Formula) (i c : ℕ) : ℕ :=
  if c < 3 then 2
  else if c < 3 + 2 * φ.vars then
    let v := (c - 3) / 2
    if i = 0 then 2 * v + 5
    else if i = 1 then 2
    else if (c - 3) % 2 = 0 then 10 * v + 6 else 10 * v + 11
  else
    let o := c - 3 - 2 * φ.vars
    let l := BoundedSat.litOfSlot φ o
    if i = 2 then
      (if l.2 then 10 * l.1 + 5 + 2 * BoundedSat.slotRank φ o
        else 10 * l.1 + 10 + 2 * BoundedSat.slotRank φ o)
    else if o < 2 * φ.twoClauses then
      (if i = 0 then 2 * φ.vars + 2 * (o / 2) + 7 else 2)
    else
      (if i = 0 then
        2 * φ.vars + 2 * φ.twoClauses + 2 * ((o - 2 * φ.twoClauses) / 3) + 9
      else 3 * ((o - 2 * φ.twoClauses) / 3) + 6)

theorem two_le_due (φ : BoundedSat.Formula) (i c : ℕ) : 2 ≤ due φ i c := by
  unfold due
  simp only []
  split_ifs <;> omega

/-- **The instance of Theorem 7**: three days, all processing times `2`, and the fairness
parameter `1`. -/
def inst (φ : BoundedSat.Formula) : Instance where
  clients := clients φ
  days := 3
  p _ _ := 2
  d i c := due φ i c
  p_pos _ _ := by omega
  p_le_d i c := two_le_due φ i c

/-- **The constructed instance has three days.** -/
axiom inst_days (φ : BoundedSat.Formula) : (inst φ).days = 3

end Lax117284.Theorem7
end
